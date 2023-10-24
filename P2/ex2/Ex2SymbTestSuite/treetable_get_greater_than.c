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

    void* out;
    enum cc_stat status = treetable_get_greater_than(table, &key1, &out);
    assert(status == CC_ERR_KEY_NOT_FOUND);

    enum cc_stat status2 = treetable_add(table, &key1, &value1);
    assert(status2 == CC_OK);
    
    enum cc_stat status3 = treetable_add(table, &key2, &value2);
    assert(status3 == CC_OK);

    enum cc_stat status4 = treetable_get_greater_than(table, &key1, &out);
    assert(status4 == CC_OK);
    
    treetable_destroy(table);
}