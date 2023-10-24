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
    char value2;

    klee_make_symbolic(&key1, sizeof(int), "key1");
    klee_make_symbolic(&key2, sizeof(int), "key2");
    klee_make_symbolic(&value1, sizeof(value1), "value1");
    klee_make_symbolic(&value2, sizeof(value2), "value2");

    enum cc_stat status = treetable_add(table, &key1, &value1);
    enum cc_stat status2 = treetable_add(table, &key2, &value2);

    if (status == CC_OK) {
        assert(treetable_contains_key(table, &key1));
    }
    if (status2 == CC_OK) {
        assert(treetable_contains_key(table, &key2));
        assert(treetable_contains_value(table, &value2) >= 1);
    }
    
    treetable_destroy(table);
}