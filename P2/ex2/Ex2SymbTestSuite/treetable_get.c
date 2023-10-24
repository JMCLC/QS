#include "klee/klee.h"
#include <stdio.h>
#include "../treetable.h"
#include <assert.h>

int main() {
    TreeTable *table;
    treetable_new(&table);

    int key1;
    int key2;

    char value1; 

    klee_make_symbolic(&key1, sizeof(int), "key1");
    klee_make_symbolic(&key2, sizeof(int), "key2");
    klee_make_symbolic(&value1, sizeof(value1), "value1");

    treetable_add(table, &key1, &value1);

    void *out, *out2;
    enum cc_stat status = treetable_get(table, &key1, &out);
    assert(status == CC_OK);
    assert(*((char*) out) == value1);

    enum cc_stat status2 = treetable_get(table, &key2, &out2);
    if (key1 != key2) {
        assert(status2 == CC_ERR_KEY_NOT_FOUND); 
    }

    treetable_destroy(table);
}