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

    enum cc_stat status1 = treetable_add(table, &key1, &value1);
    if (status1 == CC_OK) {
        void* out;
        enum cc_stat status2 = treetable_get_first_key(table, &out);
        assert(status2 == CC_OK);
        assert(*((int*) out) == key1);
    }

    enum cc_stat status3 = treetable_add(table, &key2, &value2);
    if (status3 == CC_OK) {
        void* out;
        enum cc_stat status4 = treetable_get_first_key(table, &out);
        assert(status4 == CC_OK);
        if (key1 <= key2) {
            assert(*((int*) out) == key1);
        } else {
            assert(*((int*) out) == key2);
        }
    }
    
    treetable_destroy(table);
}