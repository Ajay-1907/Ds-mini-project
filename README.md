#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <ctype.h>

#define MAX_BAYS    3
#define HASH_SIZE   11
#define STACK_MAX   50
#define NLOC        6
#define NSERV       5
#define GST_RATE    0.18

#define VEH_FILE "vehicles.txt"
#define JOB_FILE "jobs.txt"
#define PAY_FILE "payments.txt"
#define RPT_FILE "report.txt"

/* ----------------------------- data types ------------------------------ */
enum { WAITING, IN_SERVICE, COMPLETED, PAID, CANCELLED };
static const char *statusName[] = { "Waiting", "In Service", "Completed", "Paid", "Cancelled" };

typedef struct { const char *name; double charge; } ServiceType;
static const ServiceType services[NSERV] = {          /* ARRAY (price table) */
    { "Oil Change",      800.0 },
    { "Wheel Alignment", 1200.0 },
    { "Brake Service",   1500.0 },
    { "Full Service",    3500.0 },
    { "Engine Repair",   6000.0 }
};

typedef struct Vehicle {                  /* one record, two indexes: hash + BST */
    char no[16], owner[32], phone[16], type[10];
    struct Vehicle *hnext;                /* hash chain  */
    struct Vehicle *left, *right;         /* BST links   */
} Vehicle;

typedef struct Job {                      /* SINGLY LINKED LIST node */
    int id;
    char vno[16];
    int svc;                              /* index in services[] */
    double charge;
    int status;
    int bay;                              /* -1 if no bay */
    time_t booked, in, out;
    struct Job *next;
} Job;

typedef struct Hist {                     /* DOUBLY LINKED LIST node */
    Job *job;
    struct Hist *prev, *next;
} Hist;

typedef struct QNode {                    /* QUEUE node */
    Job *job;
    struct QNode *next;
} QNode;

enum { A_REG, A_BOOK, A_COMPLETE, A_PAY, A_CANCEL };
typedef struct { int type; int id; char vno[16]; } Action;   /* STACK element */

/* ------------------------------- globals ------------------------------- */
static Vehicle *htab[HASH_SIZE];                     /* hash table       */
static Vehicle *root;                                /* BST root         */
static int vcount;
static Job *jhead, *jtail;                           /* job list         */
static int nextJob = 1001;
static int bays[MAX_BAYS];                           /* 0 = free         */
static QNode *qfront, *qrear;                        /* waiting queue    */
static Hist *hhead, *htail;                          /* history list     */
static Action stk[STACK_MAX];
static int top = -1;                                 /* stack top        */

static const char *loc[NLOC] = { "Reception", "Inspection Area", "Service Bay Area",
                                 "Washing Area", "Spare Parts Store", "Delivery Point" };
static int graph[NLOC][NLOC];                        /* adjacency matrix */

/* ------------------------------ utilities ------------------------------ */
static void readLine(const char *prompt, char *buf, int n)
{
    printf("%s", prompt);
    fflush(stdout);
    if (!fgets(buf, n, stdin)) { buf[0] = '\0'; return; }
    buf[strcspn(buf, "\r\n")] = '\0';
}

static int readInt(const char *prompt)
{
    char b[32];
    readLine(prompt, b, sizeof b);
    return atoi(b);
}

static void toKey(char *s)                    /* upper-case, remove spaces */
{
    char *d = s;
    for (; *s; s++)
        if (!isspace((unsigned char)*s)) *d++ = (char)toupper((unsigned char)*s);
    *d = '\0';
}

static void fmtTime(time_t t, char *b, size_t n)
{
    if (t == 0) { snprintf(b, n, "--:--:--"); return; }
    strftime(b, n, "%H:%M:%S", localtime(&t));
}

static void line(void) { printf("  ----------------------------------------------------------------------\n"); }

/* ------------------------------ hash table ----------------------------- */
static unsigned hashFn(const char *k)
{
    unsigned h = 0;
    while (*k) h = h * 31u + (unsigned char)*k++;
    return h % HASH_SIZE;
}

static Vehicle *hashFind(const char *k)
{
    Vehicle *v = htab[hashFn(k)];
    while (v && strcmp(v->no, k)) v = v->hnext;
    return v;
}

static void hashInsert(Vehicle *v)
{
    unsigned i = hashFn(v->no);
    v->hnext = htab[i];
    htab[i] = v;
}

/* --------------------------- binary search tree ------------------------ */
static Vehicle *bstInsert(Vehicle *r, Vehicle *v)
{
    if (!r) return v;
    if (strcmp(v->no, r->no) < 0) r->left = bstInsert(r->left, v);
    else                          r->right = bstInsert(r->right, v);
    return r;
}

static Vehicle *bstSearch(Vehicle *r, const char *k, int *steps)
{
    while (r) {
        (*steps)++;
        int c = strcmp(k, r->no);
        if (c == 0) return r;
        r = (c < 0) ? r->left : r->right;
    }
    return NULL;
}

static Vehicle *bstMin(Vehicle *r) { while (r && r->left)  r = r->left;  return r; }
static Vehicle *bstMax(Vehicle *r) { while (r && r->right) r = r->right; return r; }

static int bstCollect(Vehicle *r, Vehicle **arr, int i)       /* in-order */
{
    if (!r) return i;
    i = bstCollect(r->left, arr, i);
    arr[i++] = r;
    return bstCollect(r->right, arr, i);
}

static void printVehicleRow(const Vehicle *v)
{
    printf("  %-12s %-18s %-12s %-6s\n", v->no, v->owner, v->phone, v->type);
}

static Vehicle *addVehicle(const char *no, const char *owner, const char *phone, const char *type)
{
    Vehicle *v = calloc(1, sizeof *v);
    if (!v) { printf("  [!] Out of memory.\n"); exit(1); }
    snprintf(v->no, sizeof v->no, "%s", no);
    snprintf(v->owner, sizeof v->owner, "%s", owner);
    snprintf(v->phone, sizeof v->phone, "%s", phone);
    snprintf(v->type, sizeof v->type, "%s", type);
    hashInsert(v);
    root = bstInsert(root, v);
    vcount++;
    return v;
}

/* --------------------------------- stack ------------------------------- */
static void push(int type, int id, const char *vno)
{
    if (top == STACK_MAX - 1) {                              /* drop oldest */
        memmove(&stk[0], &stk[1], sizeof(Action) * (STACK_MAX - 1));
        top--;
    }
    top++;
    stk[top].type = type;
    stk[top].id = id;
    snprintf(stk[top].vno, sizeof stk[top].vno, "%s", vno);
}

static const char *actionName(int t)
{
    switch (t) {
        case A_REG:      return "Register vehicle";
        case A_BOOK:     return "Book service";
        case A_COMPLETE: return "Complete service";
        case A_PAY:      return "Payment";
        default:         return "Cancel service";
    }
}

/* --------------------------------- queue ------------------------------- */
static void enqueue(Job *j)
{
    QNode *n = malloc(sizeof *n);
    if (!n) exit(1);
    n->job = j; n->next = NULL;
    if (!qrear) qfront = qrear = n;
    else { qrear->next = n; qrear = n; }
}

static Job *dequeue(void)
{
    if (!qfront) return NULL;
    QNode *n = qfront;
    Job *j = n->job;
    qfront = n->next;
    if (!qfront) qrear = NULL;
    free(n);
    return j;
}

static int queueLength(void)
{
    int c = 0;
    for (QNode *q = qfront; q; q = q->next) c++;
    return c;
}

static void queueRemove(Job *j)
{
    QNode *cur = qfront, *prev = NULL;
    while (cur && cur->job != j) { prev = cur; cur = cur->next; }
    if (!cur) return;
    if (prev) prev->next = cur->next; else qfront = cur->next;
    if (cur == qrear) qrear = prev;
    free(cur);
}

/* ------------------------------ job list ------------------------------- */
static void appendJob(Job *j)
{
    j->next = NULL;
    if (!jhead) jhead = jtail = j;
    else { jtail->next = j; jtail = j; }
}

static Job *findJob(int id)                                  /* linear search */
{
    for (Job *j = jhead; j; j = j->next)
        if (j->id == id) return j;
    return NULL;
}

static void histAdd(Job *j)
{
    Hist *h = calloc(1, sizeof *h);
    if (!h) exit(1);
    h->job = j;
    if (!htail) hhead = htail = h;
    else { htail->next = h; h->prev = htail; htail = h; }
}

/* ------------------------------- file I/O ------------------------------ */
static void saveAll(void)
{
    FILE *fv = fopen(VEH_FILE, "w");
    if (fv) {
        Vehicle **arr = malloc(sizeof(Vehicle *) * (vcount ? vcount : 1));
        int n = arr ? bstCollect(root, arr, 0) : 0;
        for (int i = 0; i < n; i++)
            fprintf(fv, "%s|%s|%s|%s\n", arr[i]->no, arr[i]->owner, arr[i]->phone, arr[i]->type);
        free(arr);
        fclose(fv);
    } else printf("  [!] Could not write %s\n", VEH_FILE);

    FILE *fj = fopen(JOB_FILE, "w");
    if (fj) {
        for (Job *j = jhead; j; j = j->next)
            fprintf(fj, "%d|%s|%d|%.2f|%d|%ld|%ld|%ld|%d\n", j->id, j->vno, j->svc, j->charge,
                    j->status, (long)j->booked, (long)j->in, (long)j->out, j->bay);
        fclose(fj);
    } else printf("  [!] Could not write %s\n", JOB_FILE);
}

static void loadAll(void)
{
    char buf[256];
    int vloaded = 0, jloaded = 0;
    FILE *fv = fopen(VEH_FILE, "r");
    if (fv) {
        while (fgets(buf, sizeof buf, fv)) {
            char no[16], ow[32], ph[16], ty[10];
            if (sscanf(buf, "%15[^|]|%31[^|]|%15[^|]|%9[^\n]", no, ow, ph, ty) == 4) {
                addVehicle(no, ow, ph, ty);
                vloaded++;
            }
        }
        fclose(fv);
    }
    FILE *fj = fopen(JOB_FILE, "r");
    if (fj) {
        while (fgets(buf, sizeof buf, fj)) {
            Job t; long b, i, o;
            memset(&t, 0, sizeof t);
            if (sscanf(buf, "%d|%15[^|]|%d|%lf|%d|%ld|%ld|%ld|%d", &t.id, t.vno, &t.svc,
                       &t.charge, &t.status, &b, &i, &o, &t.bay) == 9) {
                Job *j = malloc(sizeof *j);
                if (!j) exit(1);
                *j = t; j->booked = b; j->in = i; j->out = o;
                appendJob(j);
                if (j->id >= nextJob) nextJob = j->id + 1;
                if (j->status == IN_SERVICE && j->bay >= 0 && j->bay < MAX_BAYS) bays[j->bay] = j->id;
                else if (j->status == WAITING) enqueue(j);
                else if (j->status == COMPLETED || j->status == PAID) histAdd(j);
                jloaded++;
            }
        }
        fclose(fj);
    }
    if (vloaded || jloaded)
        printf("  [File] Loaded %d vehicle(s) and %d job(s) from disk.\n", vloaded, jloaded);
    else
        printf("  [File] No saved data found - starting with an empty system.\n");
}

/* ---------------------------- core operations -------------------------- */
static int assignBay(Job *j)
{
    for (int i = 0; i < MAX_BAYS; i++)
        if (bays[i] == 0) {
            bays[i] = j->id;
            j->bay = i;
            j->status = IN_SERVICE;
            j->in = time(NULL);
            return 1;
        }
    return 0;
}

static void promoteWaiting(void)
{
    while (qfront) {
        int free_bay = 0;
        for (int i = 0; i < MAX_BAYS; i++) if (bays[i] == 0) free_bay = 1;
        if (!free_bay) break;
        Job *j = dequeue();
        assignBay(j);
        printf("  [Queue] Job #%d (%s) moved from waiting queue to Bay %d.\n", j->id, j->vno, j->bay + 1);
    }
}

static Vehicle *registerVehicle(const char *no, const char *owner, const char *phone, const char *type)
{
    char key[16];
    snprintf(key, sizeof key, "%s", no);
    toKey(key);
    if (!key[0]) { printf("  [!] Vehicle number cannot be empty.\n"); return NULL; }
    if (hashFind(key)) { printf("  [!] Duplicate vehicle number %s - already registered.\n", key); return NULL; }
    Vehicle *v = addVehicle(key, owner, phone, type);
    push(A_REG, 0, key);
    saveAll();
    printf("  [OK] Vehicle %s registered for %s.\n", key, owner);
    return v;
}

static Job *bookService(const char *vno, int svc)
{
    char key[16];
    snprintf(key, sizeof key, "%s", vno);
    toKey(key);
    if (!hashFind(key)) { printf("  [!] Vehicle %s is not registered.\n", key); return NULL; }
    if (svc < 1 || svc > NSERV) { printf("  [!] Invalid service type.\n"); return NULL; }
    for (Job *p = jhead; p; p = p->next)
        if (!strcmp(p->vno, key) && (p->status == WAITING || p->status == IN_SERVICE)) {
            printf("  [!] Repeated booking: %s already has active job #%d.\n", key, p->id);
            return NULL;
        }
    Job *j = calloc(1, sizeof *j);
    if (!j) exit(1);
    j->id = nextJob++;
    snprintf(j->vno, sizeof j->vno, "%s", key);
    j->svc = svc - 1;
    j->charge = services[svc - 1].charge;
    j->booked = time(NULL);
    j->bay = -1;
    j->status = WAITING;
    appendJob(j);
    if (assignBay(j))
        printf("  [OK] Job #%d booked: %s - %s. Bay %d allocated.\n", j->id, key, services[j->svc].name, j->bay + 1);
    else {
        enqueue(j);
        printf("  [OK] Job #%d booked: %s - %s. No free bay - added to waiting queue (position %d).\n",
               j->id, key, services[j->svc].name, queueLength());
    }
    push(A_BOOK, j->id, key);
    saveAll();
    return j;
}

static void completeService(Job *j)
{
    if (!j) { printf("  [!] Invalid job id.\n"); return; }
    if (j->status != IN_SERVICE) {
        printf("  [!] Job #%d is '%s' - only jobs 'In Service' can be completed.\n", j->id, statusName[j->status]);
        return;
    }
    bays[j->bay] = 0;
    j->status = COMPLETED;
    j->out = time(NULL);
    histAdd(j);
    push(A_COMPLETE, j->id, j->vno);
    printf("  [OK] Job #%d (%s) completed. Bay %d released.\n", j->id, j->vno, j->bay + 1);
    promoteWaiting();
    saveAll();
}

static void cancelJob(Job *j, int record)
{
    if (!j) { printf("  [!] Invalid job id.\n"); return; }
    if (j->status == WAITING) queueRemove(j);
    else if (j->status == IN_SERVICE) bays[j->bay] = 0;
    else { printf("  [!] Job #%d is '%s' and cannot be cancelled.\n", j->id, statusName[j->status]); return; }
    j->status = CANCELLED;
    j->bay = -1;
    printf("  [OK] Job #%d (%s) cancelled.\n", j->id, j->vno);
    if (record) push(A_CANCEL, j->id, j->vno);
    promoteWaiting();
    saveAll();
}

static void payBill(Job *j)
{
    if (!j) { printf("  [!] Invalid job id.\n"); return; }
    if (j->status != COMPLETED) {
        printf("  [!] Job #%d is '%s' - bill can be paid only for 'Completed' jobs.\n", j->id, statusName[j->status]);
        return;
    }
    double gst = j->charge * GST_RATE, total = j->charge + gst;
    long secs = (long)(j->out - j->in);
    char tin[16], tout[16];
    fmtTime(j->in, tin, sizeof tin);
    fmtTime(j->out, tout, sizeof tout);
    printf("\n  +--------------------------------------------------+\n");
    char title[40];
    snprintf(title, sizeof title, "SERVICE BILL  -  Job #%d", j->id);
    printf("  |%*s%-*s|\n", 13, "", 37, title);
    printf("  +--------------------------------------------------+\n");
    printf("   Vehicle No   : %s\n", j->vno);
    printf("   Service      : %s\n", services[j->svc].name);
    printf("   Check-in     : %s     Delivery : %s\n", tin, tout);
    printf("   Duration     : %ld min %ld sec\n", secs / 60, secs % 60);
    printf("   Charge       : Rs. %9.2f\n", j->charge);
    printf("   GST (18%%)    : Rs. %9.2f\n", gst);
    printf("   TOTAL        : Rs. %9.2f\n", total);
    printf("  +--------------------------------------------------+\n");
    j->status = PAID;
    FILE *fp = fopen(PAY_FILE, "a");
    if (fp) {
        fprintf(fp, "PAID|%d|%s|%s|%.2f|%ld\n", j->id, j->vno, services[j->svc].name, total, (long)time(NULL));
        fclose(fp);
    }
    push(A_PAY, j->id, j->vno);
    printf("  [OK] Payment recorded in %s.\n", PAY_FILE);
    saveAll();
}

static void undoLast(void)
{
    if (top < 0) { printf("  [!] Nothing to undo.\n"); return; }
    Action a = stk[top--];
    printf("  Undoing: %s (%s)\n", actionName(a.type), a.vno);
    Job *j = findJob(a.id);
    switch (a.type) {
        case A_BOOK:
            if (j && (j->status == WAITING || j->status == IN_SERVICE)) cancelJob(j, 0);
            else printf("  [!] Booking #%d has progressed and can no longer be undone.\n", a.id);
            break;
        case A_PAY:
            if (j && j->status == PAID) {
                j->status = COMPLETED;
                FILE *fp = fopen(PAY_FILE, "a");
                if (fp) { fprintf(fp, "REVERSED|%d|%s\n", j->id, j->vno); fclose(fp); }
                printf("  [OK] Payment for job #%d reversed - status back to 'Completed'.\n", j->id);
                saveAll();
            }
            break;
        default:
            printf("  [!] This action is permanent and cannot be undone (removed from history).\n");
    }
}

/* ------------------------------- displays ------------------------------ */
static void showJob(const Job *j)
{
    char tb[16];
    fmtTime(j->booked, tb, sizeof tb);
    printf("  %-6d %-12s %-16s %9.2f  %-11s %-4s %s\n", j->id, j->vno, services[j->svc].name,
           j->charge, statusName[j->status], tb, "");
}

static void jobHeader(void)
{
    printf("  %-6s %-12s %-16s %9s  %-11s %-4s\n", "JobID", "Vehicle", "Service", "Charge", "Status", "Booked");
    line();
}

static void viewBays(void)
{
    printf("\n  SERVICE BAYS (array of %d)\n", MAX_BAYS);
    line();
    for (int i = 0; i < MAX_BAYS; i++) {
        if (bays[i]) {
            Job *j = findJob(bays[i]);
            printf("   Bay %d : OCCUPIED  - Job #%d  %s  (%s)\n", i + 1, j->id, j->vno, services[j->svc].name);
        } else printf("   Bay %d : FREE\n", i + 1);
    }
}

static void viewQueue(void)
{
    printf("\n  WAITING QUEUE (FIFO)\n");
    line();
    if (!qfront) { printf("   Queue is empty.\n"); return; }
    int pos = 1;
    for (QNode *q = qfront; q; q = q->next, pos++)
        printf("   %d. Job #%d  %s  (%s)\n", pos, q->job->id, q->job->vno, services[q->job->svc].name);
}

static void viewJobs(void)
{
    printf("\n  ALL SERVICE JOBS (singly linked list)\n");
    if (!jhead) { printf("   No jobs recorded.\n"); return; }
    jobHeader();
    for (Job *j = jhead; j; j = j->next) showJob(j);
}

static void historyNavigator(void)
{
    if (!htail) { printf("  No completed services yet.\n"); return; }
    Hist *cur = htail;
    char cmd[8];
    int pos = 0;
    for (Hist *h = hhead; h; h = h->next) pos++;
    printf("\n  SERVICE HISTORY (doubly linked list) - starts at most recent\n");
    for (;;) {
        char tin[16], tout[16];
        fmtTime(cur->job->in, tin, sizeof tin);
        fmtTime(cur->job->out, tout, sizeof tout);
        printf("   [%d] Job #%d | %s | %s | Rs. %.2f | %s | in %s out %s\n", pos, cur->job->id, cur->job->vno,
               services[cur->job->svc].name, cur->job->charge, statusName[cur->job->status], tin, tout);
        readLine("   [p] older   [n] newer   [q] quit : ", cmd, sizeof cmd);
        if (cmd[0] == 'p' || cmd[0] == 'P') {
            if (cur->prev) { cur = cur->prev; pos--; } else printf("   (already at the oldest record)\n");
        } else if (cmd[0] == 'n' || cmd[0] == 'N') {
            if (cur->next) { cur = cur->next; pos++; } else printf("   (already at the newest record)\n");
        } else break;
    }
}

static void showStackActions(void)
{
    printf("\n  RECENT ADMIN ACTIONS (stack - top first)\n");
    line();
    if (top < 0) { printf("   Stack is empty.\n"); return; }
    for (int i = top; i >= 0; i--)
        printf("   %s%-17s %-12s %s\n", i == top ? "-> " : "   ", actionName(stk[i].type), stk[i].vno,
               stk[i].id ? "(job)" : "");
}

/* ------------------------- searching & sorting ------------------------- */
static void searchVehicle(void)
{
    char key[32];
    readLine("  Enter vehicle number to search : ", key, sizeof key);
    toKey(key);
    Vehicle *v = hashFind(key);                                   /* hash */
    printf("\n  [Hash table]  bucket %u -> %s\n", hashFn(key), v ? "FOUND (O(1) average)" : "NOT FOUND");
    int steps = 0;
    Vehicle *b = bstSearch(root, key, &steps);                    /* BST */
    printf("  [BST]         %s after %d comparison(s)\n", b ? "FOUND" : "NOT FOUND", steps);

    Vehicle **arr = malloc(sizeof(Vehicle *) * (vcount ? vcount : 1));      /* binary search */
    int n = arr ? bstCollect(root, arr, 0) : 0, lo = 0, hi = n - 1, cmp = 0, pos = -1;
    while (lo <= hi) {
        int mid = (lo + hi) / 2, c = strcmp(key, arr[mid]->no);
        cmp++;
        if (c == 0) { pos = mid; break; }
        if (c > 0) lo = mid + 1; else hi = mid - 1;
    }
    printf("  [Binary search] %s in sorted array of %d (%d comparison(s))\n",
           pos >= 0 ? "FOUND" : "NOT FOUND", n, cmp);
    free(arr);
    if (!v) return;
    printf("\n  %-12s %-18s %-12s %-6s\n", "Vehicle", "Owner", "Phone", "Type");
    line();
    printVehicleRow(v);
    printf("\n  Service jobs of this vehicle (linear search):\n");
    int found = 0;
    for (Job *j = jhead; j; j = j->next)
        if (!strcmp(j->vno, key)) {
            if (!found) jobHeader();
            showJob(j);
            found = 1;
        }
    if (!found) printf("   (no service jobs yet)\n");
}

static void listVehicles(void)
{
    printf("\n  REGISTERED VEHICLES - sorted by number (BST in-order, %d record(s))\n", vcount);
    if (!root) { printf("   No vehicles registered.\n"); return; }
    printf("  %-12s %-18s %-12s %-6s\n", "Vehicle", "Owner", "Phone", "Type");
    line();
    Vehicle **arr = malloc(sizeof(Vehicle *) * vcount);
    int n = arr ? bstCollect(root, arr, 0) : 0;
    for (int i = 0; i < n; i++) printVehicleRow(arr[i]);
    free(arr);
    line();
    printf("   Minimum (leftmost) : %s\n   Maximum (rightmost): %s\n", bstMin(root)->no, bstMax(root)->no);
}

static int jobsToArray(Job **a)
{
    int n = 0;
    for (Job *j = jhead; j; j = j->next)
        if (j->status != CANCELLED) a[n++] = j;
    return n;
}

static void sortReports(void)
{
    int cnt = 0;
    for (Job *j = jhead; j; j = j->next) cnt++;
    if (!cnt) { printf("  No jobs to sort.\n"); return; }
    Job **a = malloc(sizeof(Job *) * cnt);
    if (!a) return;
    int n = jobsToArray(a);

    for (int i = 0; i < n - 1; i++)                              /* bubble sort: charge desc */
        for (int k = 0; k < n - i - 1; k++)
            if (a[k]->charge < a[k + 1]->charge) { Job *t = a[k]; a[k] = a[k + 1]; a[k + 1] = t; }
    printf("\n  JOBS SORTED BY SERVICE CHARGE (Bubble Sort, highest first)\n");
    jobHeader();
    for (int i = 0; i < n; i++) showJob(a[i]);

    n = jobsToArray(a);                                          /* insertion sort: booking time asc */
    for (int i = 1; i < n; i++) {
        Job *key = a[i];
        int k = i - 1;
        while (k >= 0 && a[k]->booked > key->booked) { a[k + 1] = a[k]; k--; }
        a[k + 1] = key;
    }
    printf("\n  JOBS SORTED BY BOOKING TIME (Insertion Sort, earliest first)\n");
    jobHeader();
    for (int i = 0; i < n; i++) showJob(a[i]);
    free(a);
}

/* --------------------------------- graph ------------------------------- */
static void initGraph(void)
{
    int e[][2] = { {0,1}, {1,2}, {1,4}, {2,3}, {2,4}, {3,5} };
    for (int i = 0; i < 6; i++) graph[e[i][0]][e[i][1]] = graph[e[i][1]][e[i][0]] = 1;
}

static void dfsRec(int v, int *vis)
{
    vis[v] = 1;
    printf("%s%s", v == 0 ? "" : " -> ", loc[v]);
    for (int i = 0; i < NLOC; i++)
        if (graph[v][i] && !vis[i]) dfsRec(i, vis);
}

static void layoutGraph(void)
{
    printf("\n  SERVICE CENTRE LAYOUT (graph - adjacency matrix)\n");
    line();
    for (int i = 0; i < NLOC; i++) {
        printf("   %d %-18s connects to :", i, loc[i]);
        for (int k = 0; k < NLOC; k++) if (graph[i][k]) printf(" %d", k);
        printf("\n");
    }
    int s = readInt("\n  Start location (0-5) : ");
    if (s < 0 || s >= NLOC) { printf("  [!] Invalid location.\n"); return; }
    int vis[NLOC] = {0}, q[NLOC], f = 0, r = 0;
    vis[s] = 1; q[r++] = s;
    printf("\n  BFS (nearby areas first): ");
    while (f < r) {
        int v = q[f++];
        printf("%s%s", f == 1 ? "" : " -> ", loc[v]);
        for (int i = 0; i < NLOC; i++)
            if (graph[v][i] && !vis[i]) { vis[i] = 1; q[r++] = i; }
    }
    memset(vis, 0, sizeof vis);
    printf("\n  DFS (deep path first)   : ");
    dfsRec(s, vis);
    printf("\n");
}

/* --------------------------------- report ------------------------------ */
static void writeReport(void)
{
    int c[5] = {0}, total = 0;
    double revenue = 0;
    for (Job *j = jhead; j; j = j->next) {
        c[j->status]++;
        total++;
        if (j->status == PAID) revenue += j->charge * (1 + GST_RATE);
    }
    int occupied = 0;
    for (int i = 0; i < MAX_BAYS; i++) if (bays[i]) occupied++;
    time_t now = time(NULL);
    char ts[32];
    strftime(ts, sizeof ts, "%d-%m-%Y %H:%M:%S", localtime(&now));

    FILE *fp = fopen(RPT_FILE, "w");
    FILE *out[2] = { stdout, fp };
    for (int k = 0; k < 2; k++) {
        if (!out[k]) continue;
        fprintf(out[k], "\n  ======== VEHICLE SERVICE MANAGEMENT - SUMMARY REPORT ========\n");
        fprintf(out[k], "   Generated on       : %s\n", ts);
        fprintf(out[k], "   Registered vehicles: %d\n", vcount);
        fprintf(out[k], "   Total job cards    : %d\n", total);
        fprintf(out[k], "     Waiting          : %d\n     In Service       : %d\n", c[WAITING], c[IN_SERVICE]);
        fprintf(out[k], "     Completed (unpaid): %d\n     Paid             : %d\n     Cancelled        : %d\n",
                c[COMPLETED], c[PAID], c[CANCELLED]);
        fprintf(out[k], "   Bays occupied      : %d / %d\n", occupied, MAX_BAYS);
        fprintf(out[k], "   Revenue collected  : Rs. %.2f (incl. GST)\n", revenue);
        fprintf(out[k], "  =============================================================\n");
    }
    if (fp) { fclose(fp); printf("  [File] Report saved to %s\n", RPT_FILE); }
}

/* ------------------------------- demo data ----------------------------- */
static void loadDemo(void)
{
    printf("\n  Loading demo data...\n");
    registerVehicle("TN37AB1234", "Arun Kumar",    "9876543210", "Car");
    registerVehicle("TN38CD5678", "Meena Devi",    "9123456780", "Bike");
    registerVehicle("TN66EF9012", "Ravi Shankar",  "9988776655", "Car");
    registerVehicle("TN41GH3456", "Priya Nair",    "9090909090", "Truck");
    registerVehicle("TN37JK7788", "Karthik Raj",   "9345678123", "Bike");
    bookService("TN37AB1234", 4);
    bookService("TN38CD5678", 1);
    bookService("TN66EF9012", 3);
    bookService("TN41GH3456", 2);
    bookService("TN37JK7788", 5);
}

/* ---------------------------------- menu ------------------------------- */
static void menu(void)
{
    printf("\n  ==================================================\n");
    printf("      VEHICLE SERVICE MANAGEMENT SYSTEM\n");
    printf("  ==================================================\n");
    printf("   1. Register Vehicle            9. Search Vehicle (Hash/BST/Binary)\n");
    printf("   2. Book Service               10. List Vehicles (sorted, min/max)\n");
    printf("   3. Complete Service           11. Service History (doubly linked)\n");
    printf("   4. Cancel Service             12. Sort Reports (bubble/insertion)\n");
    printf("   5. Pay Bill                   13. Service Centre Layout (BFS/DFS)\n");
    printf("   6. View Service Bays          14. Recent Actions / Undo (stack)\n");
    printf("   7. View Waiting Queue         15. Generate Report (file)\n");
    printf("   8. View All Jobs              16. Load Demo Data\n");
    printf("   0. Save and Exit\n");
}

int main(void)
{
    initGraph();
    printf("\n  Vehicle Service Management System - CIET U23CSP03\n");
    loadAll();

    for (;;) {
        menu();
        int ch = readInt("\n  Enter your choice : ");
        switch (ch) {
        case 1: {
            char no[32], ow[32], ph[16], ty[10];
            readLine("  Vehicle number  : ", no, sizeof no);
            readLine("  Owner name      : ", ow, sizeof ow);
            readLine("  Phone           : ", ph, sizeof ph);
            readLine("  Type (Car/Bike/Truck) : ", ty, sizeof ty);
            registerVehicle(no, ow, ph, ty);
            break;
        }
        case 2: {
            char no[32];
            readLine("  Vehicle number : ", no, sizeof no);
            printf("  Service types:\n");
            for (int i = 0; i < NSERV; i++) printf("    %d. %-16s Rs. %.2f\n", i + 1, services[i].name, services[i].charge);
            bookService(no, readInt("  Choose service : "));
            break;
        }
        case 3: completeService(findJob(readInt("  Job id to complete : "))); break;
        case 4: cancelJob(findJob(readInt("  Job id to cancel : ")), 1); break;
        case 5: payBill(findJob(readInt("  Job id to pay : "))); break;
        case 6: viewBays(); break;
        case 7: viewQueue(); break;
        case 8: viewJobs(); break;
        case 9: searchVehicle(); break;
        case 10: listVehicles(); break;
        case 11: historyNavigator(); break;
        case 12: sortReports(); break;
        case 13: layoutGraph(); break;
        case 14: {
            showStackActions();
            if (top >= 0) {
                char a[8];
                readLine("\n  Undo the latest action? (y/n) : ", a, sizeof a);
                if (a[0] == 'y' || a[0] == 'Y') undoLast();
            }
            break;
        }
        case 15: writeReport(); break;
        case 16: loadDemo(); break;
        case 0:
            saveAll();
            printf("\n  Data saved to %s and %s. Thank you!\n\n", VEH_FILE, JOB_FILE);
            return 0;
        default:
            printf("  [!] Invalid choice. Try again.\n");
        }
    }
}

