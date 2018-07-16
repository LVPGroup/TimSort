#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <math.h>
int *a;
int *run_len,*run_base;
int stack_size, global_min_gallop, stack_len;
int gallop_left(int key, const int* array, int base, int len, int hint)
{
    int last_ofs, ofs, max_ofs, tmp_gallop, mid;
    last_ofs = 0;
    ofs = 1;
    if (key > array[base+hint]) {
        max_ofs = len - hint;
        while (ofs < max_ofs && key > array[base+hint+ofs]) {
            last_ofs = ofs;
            ofs = ofs*2 + 1; // not check overflow
        }
        if (ofs > max_ofs) {
            ofs = max_ofs;
        }
        last_ofs += hint + 1;
        ofs += hint;
    } else {
        max_ofs = hint + 1;
        while (ofs < max_ofs && key <= array[base+hint-ofs]) {
            last_ofs = ofs;
            ofs = ofs*2 + 1;
        }
        if (ofs > max_ofs) {
            ofs = max_ofs;
        }
        tmp_gallop = last_ofs;
        last_ofs = hint + 1 - ofs;
        ofs = hint - tmp_gallop;
    }
    while (last_ofs < ofs) {
        mid = (ofs+last_ofs)/2;
        if (key > array[base+mid]) {
            last_ofs = mid + 1;
        } else {
            ofs = mid;
        }
    }
    return ofs;
}

int gallop_right(int key, const int* array, int base, int len, int hint)
{
    int last_ofs, ofs, max_ofs, tmp_gallop, mid;
    last_ofs = 0;
    ofs = 1;
    if (key < array[base+hint]) {
        max_ofs = hint + 1;
        while (ofs < max_ofs && key < array[base+hint-ofs]) {
            last_ofs = ofs;
            ofs = ofs*2 + 1;
        }
        if (ofs > max_ofs) {
            ofs = max_ofs;
        }
        tmp_gallop = last_ofs;
        last_ofs = hint + 1 - ofs;
        ofs = hint - tmp_gallop;
    } else {
        max_ofs = len - hint;
        while (ofs < max_ofs && key >= array[base+hint+ofs]) {
            last_ofs = ofs;
            ofs = ofs*2 + 1;
        }
        if (ofs > max_ofs) {
            ofs = max_ofs;
        }
        last_ofs += hint + 1;
        ofs += hint;
    }
    while (last_ofs < ofs) {
        mid = (ofs + last_ofs)/2;
        if (key < array[base+mid]) {
            ofs = mid;
        } else {
            last_ofs = mid + 1;
        }
    }
    return ofs;
}

void merge_lo(int base1, int len1, int base2, int len2) {
    int* tmp;
    int cursor1, cursor2, dest, min_gallop, count1, count2;
    int brk_flag = 0; // avoid break outer
    tmp = (int*)malloc(sizeof(int) * len1);
    memset(tmp, 0, len1);
    memcpy(tmp, &a[base1], sizeof(int) * len1);
    cursor1 = 0;
    cursor2 = base2;
    dest = base1;
    a[dest++] = a[cursor2++];
    len2--;
    min_gallop = global_min_gallop;
    if (len2 == 0) {
        memcpy(&a[dest], &tmp[cursor1], sizeof(int) * len1);
        return;
    }
    if (len1 == 1) {
        memcpy(&a[dest], &a[cursor2], sizeof(int) * len2);
        a[dest+len2] = tmp[cursor1];
        return;
    }
    while (1) {
        count1 = 0;
        count2 = 0;
        while (count1 < min_gallop && count2 < min_gallop) {
            if (a[cursor2] < tmp[cursor1]) {
                a[dest++] = a[cursor2++];
                count2++;
                count1 = 0;
                len2--;
                if (len2 == 0) {
                    brk_flag = 1;
                    break;
                }
            } else {
                a[dest++] = tmp[cursor1++];
                count1++;
                count2 = 0;
                len1--;
                if (len1 == 1) {
                    brk_flag = 1;
                    break;
                }
            }
        }
        if (brk_flag == 1) {
            break;
        }
        while (count1 >= min_gallop || count2 >= min_gallop) {
            count1 = gallop_right(a[cursor2], tmp, cursor1, len1, 0);
            if (count1 != 0) {
                memcpy(&a[dest], &tmp[cursor1], sizeof(int) * count1);
                dest += count1;
                cursor1 += count1;
                len1 -= count1;
                if (len1 <= 1) {
                    brk_flag = 1;
                    break;
                }
            }
            a[dest++] = a[cursor2++];
            len2--;
            if (len2 == 0) {
                brk_flag = 1;
                break;
            }
            count2 = gallop_left(tmp[cursor1], a, cursor2, len2, 0);
            if (count2 != 0) {
                memcpy(&a[dest], &a[cursor2], sizeof(int) * count2);
                dest += count2;
                cursor2 += count2;
                len2 -= count2;
                if (len2 == 0) {
                    brk_flag = 1;
                    break;
                }
            }
            a[dest++] = tmp[cursor1++];
            len1--;
            if (len1 == 1) {
                brk_flag = 1;
                break;
            }
            min_gallop--;
        }
        if (brk_flag == 1) {
            break;
        }
        if (min_gallop < 0) {
            min_gallop = 0;
        }
        min_gallop += 2;
    }
    if (len1 == 1) {
        memcpy(&a[dest], &a[cursor2], sizeof(int) * len2);
        a[dest+len2] = tmp[cursor1];
    } else if (len1 == 0) {
        printf("error:len1 == 0\n");
    } else {
        memcpy(&a[dest], &tmp[cursor1], sizeof(int) * len1);
    }

}

void merge_hi(int base1, int len1, int base2, int len2)
{
    int* tmp;
    int cursor1, cursor2, dest, min_gallop, count1, count2, count_tmp;
    int brk_flag = 0;
    tmp = (int*)malloc(sizeof(int) * len2);
    memcpy(tmp, &a[base2], sizeof(int) * len2);
    cursor1 = base1 + len1 - 1;
    cursor2 = len2 - 1;
    dest = base2 + len2 - 1;
    a[dest--] = a[cursor1--];
    len1--;
    min_gallop = global_min_gallop;
    if (len1 == 0) {
        memcpy(&a[dest-(len2-1)], tmp, sizeof(int) * len2);
        return;
    }
    if (len2 == 1) {
        dest -= len1;
        cursor1 -= len1;
        memcpy(&a[dest+1], &a[cursor1+1], sizeof(int) * len1);
        a[dest] = tmp[cursor2];
        return;
    }
    while (1) {
        count1 = 0;
        count2 = 0;
        while (count1 < min_gallop && count2 < min_gallop) {
            if (tmp[cursor2] < a[cursor1]) {
                a[dest--] = a[cursor1--];
                count1++;
                count2 = 0;
                len1--;
                if (len1 == 0) {
                    brk_flag = 1;
                    break;
                }
            } else {
                a[dest--] = tmp[cursor2--];
                count2++;
                count1 = 0;
                len2--;
                if (len2 == 1) {
                    brk_flag = 1;
                    break;
                }
            }
        }
        if (brk_flag == 1) {
            break;
        }
        while (count1 >= min_gallop || count2 >= min_gallop) {
            count_tmp = gallop_right(tmp[cursor2], a, base1, len1, len1-1);
            count1 = len1 - count_tmp;
            if (count1 != 0) {
                dest -= count1;
                cursor1 -= count1;
                len1 -= count1;
                memcpy(&a[dest+1], &a[cursor1+1], sizeof(int) * count1);
                if (len1 == 0) {
                    brk_flag = 1;
                    break;
                }
            }
            a[dest--] = tmp[cursor2--];
            len2--;
            if (len2 == 1) {
                brk_flag = 1;
                break;
            }
            count_tmp = gallop_left(a[cursor1], tmp, 0, len2, len2-1);
            count2 = len2 - count_tmp;
            if (count2 != 0) {
                dest -= count2;
                cursor2 -= count2;
                len2 -= count2;
                memcpy(&a[dest+1], &tmp[cursor2+1], sizeof(int) * count2);
                if (len2 <= 1) {
                    brk_flag = 1;
                    break;
                }
            }
            a[dest--] = a[cursor1--];
            len1--;
            if (len1 == 0) {
                brk_flag = 1;
                break;
            }
            min_gallop--;
        }
        if (brk_flag == 1) {
            break;
        }
        if (min_gallop < 0) {
            min_gallop = 0;
        }
        min_gallop += 2;
    }
    if (len2 == 1) {
        dest -= len1;
        cursor1 -= len1;
        memcpy(&a[dest+1], &a[cursor1+1], sizeof(int) * len1);
        a[dest] = tmp[cursor2];
    } else if (len2 == 0) {
        printf("error:len2 == 0\n");
    } else {
        memcpy(&a[dest-(len2-1)], &tmp[0], sizeof(int) * len2);
    }
}

void merge_at(int i)
{
    int k, base1, base2, len1, len2;
    base1 = run_base[i];
    len1 = run_len[i];
    base2 = run_base[i+1];
    len2 = run_len[i+1];
    // if (check_sort(a, base1, len1) == 1) {
    //     printf("run1 not sorted\n");
    // }
    // if (check_sort(a, base2, len2) == 1) {
    //     printf("run2 not sorted\n");
    // }
    run_len[i] = len1 + len2;
    if (i == stack_size - 3) {
        run_base[i+1] = run_base[i+2];
        run_len[i+1] = run_len[i+2];
    }
    stack_size--;
    k = gallop_right(a[base2], a, base1, len1, 0);
    base1 += k;
    len1 -= k;
    for (int l = 0; l < len1; ++l) {
        if (a[base1+l] <= a[base2]) {
            printf("gallop right error\n");
        }
    }
    if (len1 == 0) {
        return;
    }
    len2 = gallop_left(a[base1+len1-1], a, base2, len2, len2-1);
    for (int j = 0; j < len2; ++j) {
        if (a[base2+j] >= a[base1+len1-1]) {
            printf("gallop left error\n");
        }
    }
    if (len2 == 0) {
        return;
    }
    if (len1 <= len2) {
        merge_lo(base1, len1, base2, len2);
        // if (check_sort(a, base1, len1+len2) == 1) {
        //     printf("merge lo wrong\n");
        // }
    } else {
        merge_hi(base1, len1, base2, len2);
        // if (check_sort(a, base1, len1+len2) == 1) {
        //     printf("merge hi wrong\n");
        // }
    }

}

void merge_collapse()
{
    int n;
    while (stack_size > 1) {
        n = stack_size - 2;
        if ((n > 0 && run_len[n-1] < run_len[n] + run_len[n+1]) ||
            (n > 1 && run_len[n-2] < run_len[n-1] + run_len[n])) {
            if (run_len[n-1] < run_len[n+1]) {
                n--;
            }
        } else {
            if (n < 0 || run_len[n] > run_len[n+1]) {
                break;
            }
        }
        merge_at(n);
    }
}

void push_run(int run_base_i, int run_len_i)
{
    run_base[stack_size] = run_base_i;
    run_len[stack_size] = run_len_i;
    stack_size++;
}

void merge_force_collapse()
{
    int n;
    while (stack_size > 1) {
        n = stack_size - 2;
        if (n > 0 && run_len[n-1] < run_len[n+1]) {
            n--;
        }
        merge_at(n);
    }
}

void reverse_range(int *array, int lo, int hi)
{
    int t;
    hi--;
    while (lo < hi) {
        t = array[lo];
        array[lo] = array[hi];
        array[hi] = t;
        lo++;
        hi--;
    }
}

int count_run_and_make_ascending(int *array, int lo, int hi)
{
    int run_hi;
    run_hi = lo + 1;
    if (run_hi == hi) {
        return 1;
    }
    if (array[run_hi] < array[lo]) {
        run_hi++;
        while (run_hi < hi && array[run_hi] < array[run_hi-1]) {
            run_hi++;
        }
        reverse_range(array, lo, run_hi);
    } else {
        run_hi++;
        while (run_hi < hi && array[run_hi] >= array[run_hi-1]) {
            run_hi++;
        }
    }
    return run_hi - lo;
}

void binary_sort(int *array, int lo, int hi, int start)
{
    int pivot, left, right, mid, move;
    if (start == lo) {
        start++;
    }
    while (start < hi) {
        pivot = array[start];
        left = lo;
        right = start;
        while (left < right) {
            mid = (left + right)/2;
            if (pivot < array[mid]) {
                right = mid;
            } else {
                left = mid + 1;
            }
        }
        move = start - left;
        memcpy(&array[left+1], &array[left], sizeof(int) * move);
        array[left] = pivot;
        start++;
    }
}

void timsort(int *array, int array_len)
{
    int lo = 0, hi = array_len;
    int min_run, n_remaining, run_len_i, force, init_run_len_i;
    n_remaining = hi - lo;
    if (n_remaining < 2) {
        return;
    }
    if (n_remaining < 32) {
        init_run_len_i = count_run_and_make_ascending(array, lo, hi);
        binary_sort(array, lo, hi, lo+init_run_len_i);
        return;
    }
    a = array;
    stack_size = 0;
    min_run = 16;
    global_min_gallop = 7;
    if (array_len < 120) {
        stack_len = 4;
    } else if (array_len < 1542) {
        stack_len = 9;
    } else if (array_len < 119151) {
        stack_len = 18;
    } else {
        stack_len = 39;
    }
    run_len = (int*)malloc(sizeof(int) * stack_len);
    run_base = (int*)malloc(sizeof(int) * stack_len);
    while (n_remaining != 0) {
        run_len_i = count_run_and_make_ascending(a, lo, hi);
//        printf("%d\n",run_len_i);
        if (run_len_i < min_run) {
            if (n_remaining <= min_run) {
                force = n_remaining;
            } else {
                force = min_run;
            }
            binary_sort(a, lo, lo+force, lo+run_len_i);
            run_len_i = force;
        }
        push_run(lo, run_len_i);
        merge_collapse();
        lo += run_len_i;
        n_remaining -= run_len_i;
    }
    merge_force_collapse();
}

int check_sort(const int *qa, const int *ta, int start, int lenght)
{
    int i;
    for (i = start; i < lenght; ++i) {
        if (qa[i] != ta[i]) {
            return 1;
        }
    }
    return 0;
}
int cmpfunc (const void * a, const void * b) {
    return ( *(int*)a - *(int*)b );
}

int main(int argc, char const *argv[])
{
    int *test_array;
    int gen_time,gen_max,step_max;
    int *timsort_res;
    int *quicksort_res;
    int i,j;
    int *gen_length;
    int array_length = 0;
    gen_time = 500000;
    gen_max = 100;
    step_max = 100;
    srand48(time(NULL));
    gen_length = (int*)malloc(gen_time* sizeof(int));
    gen_length[0] = 0;
    for (i = 1; i < gen_time; ++i) {
        gen_length[i] = gen_length[i-1] + (int)(gen_max*drand48());
    }
    array_length = gen_length[i-1];
    test_array = (int*)malloc(sizeof(int) * array_length);
    for (i = 1; i < gen_time; ++i) {
        test_array[gen_length[i-1]] = 0;
        for (j = gen_length[i-1]+1; j < gen_length[i]; ++j) {
            test_array[j] = test_array[j-1] + (int)(step_max*drand48());
        }
    }
//    for (i = 0; i < gen_time; ++i) {
//        printf("%d ",gen_length[i]);
//    }
//    printf("\n");
//    for (i = 0; i < array_length; ++i) {
//        printf("%d ",test_array[i]);
//    }

    printf("length:%d\n",array_length);
    timsort_res = (int*)malloc(sizeof(int)*array_length);
    quicksort_res = (int*)malloc(sizeof(int)*array_length);
    memcpy(timsort_res, test_array, array_length* sizeof(int));
    memcpy(quicksort_res, test_array, array_length* sizeof(int));
    clock_t start = clock();
    timsort(timsort_res, array_length);
    clock_t end = clock();
    float s1 = (float)(end - start) / CLOCKS_PER_SEC;
    start = clock();
    qsort(quicksort_res, (unsigned)array_length, sizeof(int), cmpfunc);
    end = clock();
    float s2 = (float)(end - start) / CLOCKS_PER_SEC;
    if (check_sort(quicksort_res, timsort_res, 0, array_length) == 1) {
         printf("wrong\n");
     } else {
         printf("right\n");
         printf("tim:%.3f quick:%.3f",s1,s2);
     }
    return 0;
}






















