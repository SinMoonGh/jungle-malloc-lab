#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

int main(void)
{
    printf("mm_init go");
    mm_init(); // 필수!
    printf("test_remove_block_middle go");
    test_remove_block_middle();
    test_remove_block_head();
    test_remove_block_only_node();
    return 0;
}