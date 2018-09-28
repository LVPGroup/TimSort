theory TimSortProc
  imports "Simpl.Vcg" "TimSortLemma"
begin 

hoarestate globals_var = 
 stack_size:: nat
 run_base :: "nat list"
 run_len :: "nat list"
 stack_len :: nat (* length of run_len *)
 a :: "int list" (* the array to be sorted *)
 global_min_gallop :: nat


procedures (imports globals_var)
gallop_left(key::int,array::"int list",base::nat,len::nat,hint::nat|ret::nat)
where last_ofs::nat ofs::nat max_ofs::nat tmp_gallop::nat mid::nat in
"
\<acute>last_ofs:==0;;
\<acute>ofs:==1;;
IF \<acute>key>\<acute>array!(\<acute>base+\<acute>hint) 
THEN
 \<acute>max_ofs :== \<acute>len - \<acute>hint;;
 WHILE (\<acute>ofs < \<acute>max_ofs & \<acute>key > \<acute>array!(\<acute>base+\<acute>hint+\<acute>ofs))
 DO
  \<acute>last_ofs :== \<acute>ofs;;
  \<acute>ofs :== \<acute>ofs+\<acute>ofs+1
 OD ;;
 IF \<acute>ofs > \<acute>max_ofs THEN \<acute>ofs :== \<acute>max_ofs FI ;;
 \<acute>last_ofs :== \<acute>last_ofs + \<acute>hint+1;;
 \<acute>ofs :== \<acute>ofs + \<acute>hint
ELSE
 \<acute>max_ofs :== \<acute>hint + 1;;
 WHILE (\<acute>ofs < \<acute>max_ofs & \<acute>key \<le> \<acute>array!(\<acute>base+\<acute>hint-\<acute>ofs))
 DO
  \<acute>last_ofs :== \<acute>ofs;;
  \<acute>ofs :== \<acute>ofs+\<acute>ofs+1
 OD ;;
 IF \<acute>ofs > \<acute>max_ofs THEN \<acute>ofs :== \<acute>max_ofs FI ;;
 \<acute>tmp_gallop :== \<acute>last_ofs;;
 \<acute>last_ofs :== \<acute>hint+1 - \<acute>ofs;;
 \<acute>ofs :== \<acute>hint - \<acute>tmp_gallop
FI ;;
WHILE (\<acute>last_ofs < \<acute>ofs)
DO
 \<acute>mid :==  (\<acute>ofs + \<acute>last_ofs)div 2;;
 IF (\<acute>key > \<acute>array!(\<acute>base+\<acute>mid))
 THEN
  \<acute>last_ofs :== \<acute>mid+1
 ELSE
  \<acute>ofs :== \<acute>mid
 FI
OD;;
\<acute>ret :== \<acute>ofs
"

procedures (imports globals_var)
gallop_right(key::int,array::"int list",base::nat,len::nat,hint::nat|ret::nat)
where last_ofs::nat ofs::nat max_ofs::nat tmp_gallop::nat mid::nat in
"
(* \<acute>stack_len :== \<acute>stack_len;;  unnecessary but the spec need globals be modified *)
\<acute>last_ofs:==0;;
\<acute>ofs:==1;;
IF \<acute>key<\<acute>array!(\<acute>base+\<acute>hint) 
THEN
 \<acute>max_ofs :== \<acute>hint + 1;;
 WHILE (\<acute>ofs < \<acute>max_ofs & \<acute>key < \<acute>array!(\<acute>base+\<acute>hint-\<acute>ofs))
 DO
  \<acute>last_ofs :== \<acute>ofs;;
  \<acute>ofs :== \<acute>ofs+\<acute>ofs+1
 OD ;;
 IF \<acute>ofs > \<acute>max_ofs THEN \<acute>ofs :== \<acute>max_ofs FI ;;
 \<acute>tmp_gallop :== \<acute>last_ofs;;
 \<acute>last_ofs :== \<acute>hint+1 - \<acute>ofs;;
 \<acute>ofs :== \<acute>hint - \<acute>tmp_gallop
ELSE
 \<acute>max_ofs :== \<acute>len - \<acute>hint;;
 WHILE (\<acute>ofs < \<acute>max_ofs & \<acute>key \<ge> \<acute>array!(\<acute>base+\<acute>hint+\<acute>ofs))
 DO
  \<acute>last_ofs :== \<acute>ofs;;
  \<acute>ofs :== \<acute>ofs+\<acute>ofs+1
 OD ;;
 IF \<acute>ofs > \<acute>max_ofs THEN \<acute>ofs :== \<acute>max_ofs FI ;;
 \<acute>last_ofs :== \<acute>last_ofs + \<acute>hint+1;;
 \<acute>ofs :== \<acute>ofs + \<acute>hint
FI ;;
WHILE (\<acute>last_ofs < \<acute>ofs)
DO
 \<acute>mid :==  (\<acute>ofs + \<acute>last_ofs)div 2;;
 IF (\<acute>key < \<acute>array!(\<acute>base+\<acute>mid))
 THEN
  \<acute>ofs :== \<acute>mid
 ELSE
  \<acute>last_ofs :== \<acute>mid+1
 FI
OD;;
\<acute>ret :== \<acute>ofs
"


value "replicate (3::nat) (4::nat)"
value "list_copy [1,2,3::int] 6 [1,2,3::int] 1 2"
procedures (imports globals_var)
merge_lo (base1::nat, len1::nat, base2::nat, len2::nat)
where tmp::"int list" cursor1::nat cursor2::nat dest::nat 
min_gallop::nat count1::nat count2::nat in
"
TRY
  \<acute>tmp :== replicate \<acute>len1 (0::int);;
  \<acute>tmp :== list_copy \<acute>tmp (0::nat) \<acute>a \<acute>base1 \<acute>len1;;
  \<acute>cursor1 :== 0;;
  \<acute>cursor2 :==\<acute>base2;;
  \<acute>dest :== \<acute>base1;;
  \<acute>a!\<acute>dest :== \<acute>a!\<acute>cursor2;;
  \<acute>dest :== \<acute>dest+1;;
  \<acute>cursor2 :== \<acute>cursor2+1;;
  \<acute>len2 :== \<acute>len2-1;;
  \<acute>min_gallop :== \<acute>global_min_gallop;;(* need to add min gallop to globals var *)
  IF \<acute>len2=0 THEN \<acute>a :== list_copy \<acute>a \<acute>dest \<acute>tmp \<acute>cursor1 \<acute>len1;; THROW FI;;
  IF \<acute>len1=1 THEN \<acute>a :== list_copy \<acute>a \<acute>dest \<acute>a \<acute>cursor2 \<acute>len2;; \<acute>a!(\<acute>dest+\<acute>len2):== \<acute>tmp!\<acute>cursor1;;THROW FI;;
  TRY
    WHILE True 
    DO
      \<acute>count1 :== 0;;
      \<acute>count2 :== 0;;
      WHILE (\<acute>count1 < \<acute>min_gallop & \<acute>count2 < \<acute>min_gallop)
      DO
        IF \<acute>a!\<acute>cursor2 < \<acute>tmp!\<acute>cursor1
        THEN
          \<acute>a!\<acute>dest :== \<acute>a!\<acute>cursor2;;
          \<acute>dest :== \<acute>dest+1;;
          \<acute>cursor2 :== \<acute>cursor2+1;;
          \<acute>count2 :== \<acute>count2+1;;
          \<acute>count1 :== 0;;
          \<acute>len2 :== \<acute>len2-1;;
          IF \<acute>len2 = 0 THEN THROW FI
        ELSE
          \<acute>a!\<acute>dest :== \<acute>tmp!\<acute>cursor1;;
          \<acute>dest :== \<acute>dest+1;;
          \<acute>cursor1 :== \<acute>cursor1+1;;
          \<acute>count1 :== \<acute>count1+1;;
          \<acute>count2 :== 0;;
          \<acute>len1 :== \<acute>len1-1;;
          IF \<acute>len1 = 1 THEN THROW FI
        FI
      OD;;
      WHILE (\<acute>count1 \<ge> \<acute>global_min_gallop | \<acute>count2 \<ge> \<acute>global_min_gallop)
      DO
        \<acute>count1 :== CALL gallop_right(\<acute>a!\<acute>cursor2, \<acute>tmp, \<acute>cursor1, \<acute>len1, 0);;
        IF \<acute>count1 \<noteq> 0
        THEN
          \<acute>a :== list_copy \<acute>a \<acute>dest \<acute>tmp \<acute>cursor1 \<acute>count1;;
          \<acute>dest :== \<acute>dest+\<acute>count1;;
          \<acute>cursor1 :== \<acute>cursor1+\<acute>count1;;
          \<acute>len1 :== \<acute>len1-\<acute>count1;;
          IF \<acute>len1\<le>1 THEN THROW FI
        FI;;
        \<acute>a!\<acute>dest :== \<acute>a!\<acute>cursor2;;
        \<acute>dest :== \<acute>dest+1;;
        \<acute>cursor2 :== \<acute>cursor2+1;;
        \<acute>len2 :== \<acute>len2-1;;
        IF \<acute>len2 = 0 THEN THROW FI;;

        \<acute>count2 :== CALL gallop_left(\<acute>tmp!\<acute>cursor1, \<acute>a, \<acute>cursor2, \<acute>len2, 0);;
        IF \<acute>count2 \<noteq> 0
        THEN
          \<acute>a :== list_copy \<acute>a \<acute>dest \<acute>a \<acute>cursor2 \<acute>count2;;
          \<acute>dest :== \<acute>dest+\<acute>count2;;
          \<acute>cursor2 :== \<acute>cursor2+\<acute>count2;;
          \<acute>len2 :== \<acute>len2-\<acute>count2;;
          IF \<acute>len2 = 0 THEN THROW FI
        FI;;
        \<acute>a!\<acute>dest :== \<acute>tmp!\<acute>cursor1;;
        \<acute>dest :== \<acute>dest+1;;
        \<acute>cursor1 :== \<acute>cursor1+1;;
        \<acute>len1 :== \<acute>len1-1;;
        IF \<acute>len1 = 1 THEN THROW FI;;
        \<acute>min_gallop :== \<acute>min_gallop-1
      OD;;
      IF \<acute>min_gallop < 0 THEN \<acute>min_gallop :== 0 FI;;
      \<acute>min_gallop :== \<acute>min_gallop + 2
    OD
  CATCH
  Skip
  END;;
  IF \<acute>len1 = 1
  THEN \<acute>a :== list_copy \<acute>a \<acute>dest \<acute>a \<acute>cursor2 \<acute>len2;;\<acute>a!(\<acute>dest+\<acute>len2) :== \<acute>tmp!\<acute>cursor1
  ELSE IF \<acute>len1 = 0
       THEN Skip
       ELSE \<acute>a :== list_copy \<acute>a \<acute>dest \<acute>tmp \<acute>cursor1 \<acute>len1 
       FI
  FI
CATCH
Skip
END
"
procedures (imports globals_var)
merge_hi (base1::nat, len1::nat, base2::nat, len2::nat)
where tmp::"int list" cursor1::nat cursor2::nat dest::nat 
min_gallop::nat count1::nat count2::nat count_tmp::nat in
"
TRY
  \<acute>tmp :== replicate \<acute>len2 (0::int);;
  \<acute>tmp :== list_copy \<acute>tmp (0::nat) \<acute>a \<acute>base2 \<acute>len2;;
  \<acute>cursor1 :== \<acute>base1+\<acute>len1-1;;
  \<acute>cursor2 :==\<acute>len2-1;;
  \<acute>dest :== \<acute>base2+\<acute>len2-1;;
  \<acute>a!\<acute>dest :== \<acute>a!\<acute>cursor1;;
  \<acute>dest :== \<acute>dest-1;;
  \<acute>cursor1 :== \<acute>cursor1-1;;
  \<acute>len1 :== \<acute>len1-1;;
  \<acute>min_gallop :== \<acute>global_min_gallop;;(* need to add min gallop to globals var *)
  IF \<acute>len1=0 THEN \<acute>a :== list_copy \<acute>a (\<acute>dest-(\<acute>len2-1)) \<acute>tmp 0 \<acute>len2;; THROW FI;;
  IF \<acute>len2=1 
  THEN 
    \<acute>dest :== \<acute>dest-\<acute>len1;;
    \<acute>cursor1 :== \<acute>cursor1-\<acute>len1;;
    \<acute>a :== list_copy \<acute>a (\<acute>dest+1) \<acute>a (\<acute>cursor1+1) \<acute>len1;; 
    \<acute>a!\<acute>dest:== \<acute>tmp!\<acute>cursor2;;
    THROW 
  FI;;
  TRY
    WHILE True 
    DO
      \<acute>count1 :== 0;;
      \<acute>count2 :== 0;;
      WHILE (\<acute>count1 < \<acute>min_gallop & \<acute>count2 < \<acute>min_gallop)
      DO
        IF \<acute>tmp!\<acute>cursor2 < \<acute>a!\<acute>cursor1
        THEN
          \<acute>a!\<acute>dest :== \<acute>a!\<acute>cursor1;;
          \<acute>dest :== \<acute>dest-1;;
          \<acute>cursor1 :== \<acute>cursor1-1;;
          \<acute>count1 :== \<acute>count1+1;;
          \<acute>count2 :== 0;;
          \<acute>len1 :== \<acute>len1-1;;
          IF \<acute>len1 = 0 THEN THROW FI
        ELSE
          \<acute>a!\<acute>dest :== \<acute>tmp!\<acute>cursor2;;
          \<acute>dest :== \<acute>dest-1;;
          \<acute>cursor2 :== \<acute>cursor2-1;;
          \<acute>count2 :== \<acute>count2+1;;
          \<acute>count1 :== 0;;
          \<acute>len2 :== \<acute>len2-1;;
          IF \<acute>len2 = 1 THEN THROW FI
        FI
      OD;;
      WHILE (\<acute>count1 \<ge> \<acute>global_min_gallop | \<acute>count2 \<ge> \<acute>global_min_gallop)
      DO
        \<acute>count_tmp :==  CALL gallop_right(\<acute>tmp!\<acute>cursor2, \<acute>a, \<acute>base1, \<acute>len1, \<acute>len1-1);;
        \<acute>count1 :== \<acute>len1 - \<acute>count_tmp;;
        IF \<acute>count1 \<noteq> 0
        THEN
          \<acute>dest :== \<acute>dest-\<acute>count1;;
          \<acute>cursor1 :== \<acute>cursor1-\<acute>count1;;
          \<acute>len1 :== \<acute>len1-\<acute>count1;;
          \<acute>a :== list_copy \<acute>a (\<acute>dest+1) \<acute>a (\<acute>cursor1+1) \<acute>count1;;
          IF \<acute>len1=0 THEN THROW FI
        FI;;
        \<acute>a!\<acute>dest :== \<acute>tmp!\<acute>cursor2;;
        \<acute>dest :== \<acute>dest-1;;
        \<acute>cursor2 :== \<acute>cursor2-1;;
        \<acute>len2 :== \<acute>len2-1;;
        IF \<acute>len2 = 1 THEN THROW FI;;

        \<acute>count_tmp :== CALL gallop_left(\<acute>a!\<acute>cursor1, \<acute>tmp, 0, \<acute>len2, (\<acute>len2-1));;
        \<acute>count2 :== \<acute>len2 - \<acute>count_tmp;;
        IF \<acute>count2 \<noteq> 0
        THEN
          \<acute>dest :== \<acute>dest-\<acute>count2;;
          \<acute>cursor2 :== \<acute>cursor2-\<acute>count2;;
          \<acute>len2 :== \<acute>len2-\<acute>count2;;
          \<acute>a :== list_copy \<acute>a (\<acute>dest+1) \<acute>tmp (\<acute>cursor2+1) \<acute>count2;;
          IF \<acute>len2 \<le> 1 THEN THROW FI
        FI;;
        \<acute>a!\<acute>dest :== \<acute>a!\<acute>cursor1;;
        \<acute>dest :== \<acute>dest-1;;
        \<acute>cursor1 :== \<acute>cursor1-1;;
        \<acute>len1 :== \<acute>len1-1;;
        IF \<acute>len1 = 0 THEN THROW FI;;
        \<acute>min_gallop :== \<acute>min_gallop-1
      OD;;
      IF \<acute>min_gallop < 0 THEN \<acute>min_gallop :== 0 FI;;
      \<acute>min_gallop :== \<acute>min_gallop + 2
    OD
  CATCH
  Skip
  END;;
  IF \<acute>len2 = 1
  THEN 
    \<acute>dest :== \<acute>dest-\<acute>len1;;
    \<acute>cursor1 :== \<acute>cursor1-\<acute>len1;;
    \<acute>a :== list_copy \<acute>a (\<acute>dest+1) \<acute>a (\<acute>cursor1+1) \<acute>len1;;
    \<acute>a!\<acute>dest :== \<acute>tmp!\<acute>cursor2
  ELSE IF \<acute>len2 = 0
       THEN Skip
       ELSE \<acute>a :== list_copy \<acute>a (\<acute>dest-(\<acute>len2-1)) \<acute>tmp 0 \<acute>len2 
       FI
  FI
CATCH
Skip
END
"

procedures (imports globals_var)
merge_at (i::nat)
where k::nat base1::nat base2::nat len1::nat len2::nat in
"
TRY
  \<acute>base1 :== \<acute>run_base!\<acute>i;;
  \<acute>len1 :== \<acute>run_len!\<acute>i;;
  \<acute>base2 :== \<acute>run_base!(\<acute>i+1);;
  \<acute>len2 :== \<acute>run_len!(\<acute>i+1);;
  (\<acute>run_len!\<acute>i) :== \<acute>len1 + \<acute>len2;;
  IF \<acute>i=\<acute>stack_size-3
  THEN \<acute>run_base!(\<acute>i+1) :== \<acute>run_base!(\<acute>i+2);;
       \<acute>run_len!(\<acute>i+1) :==(\<acute>run_len!(\<acute>i+2)) FI;;
  \<acute>stack_size :== \<acute>stack_size-1 ;;
  (* the process of merge on the array *)
  \<acute>k :== CALL gallop_right(\<acute>a!\<acute>base2, \<acute>a, \<acute>base1, \<acute>len1, 0);;
  \<acute>base1 :== \<acute>base1+\<acute>k;;
  \<acute>len1 :== \<acute>len1-\<acute>k;;
  IF \<acute>len1=0 THEN THROW FI;;
  \<acute>len2 :== CALL gallop_left(\<acute>a!(\<acute>base1+\<acute>len1-1),\<acute>a, \<acute>base2, \<acute>len2, \<acute>len2-1);;
  IF \<acute>len2=0 THEN THROW FI;;
  IF (\<acute>len1\<le>\<acute>len2) 
  THEN CALL merge_lo(\<acute>base1, \<acute>len1, \<acute>base2, \<acute>len2)
  ELSE CALL merge_hi(\<acute>base1, \<acute>len1, \<acute>base2, \<acute>len2)
  FI
CATCH Skip END
"
print_locale merge_at_impl

procedures (imports globals_var)
merge_collapse() (* have to add something as parameter *)
where n::nat in
"TRY 
  WHILE \<acute>stack_size > 1 
  DO
    \<acute>n :== \<acute>stack_size-2;;
    IF (\<acute>n>0 \<and> \<acute>run_len!(\<acute>n-1) \<le> \<acute>run_len!\<acute>n + \<acute>run_len!(\<acute>n+1))
    \<or> (\<acute>n>1 \<and> \<acute>run_len!(\<acute>n-2) \<le> \<acute>run_len!(\<acute>n-1) + \<acute>run_len!\<acute>n)
    THEN 
      IF \<acute>run_len!(\<acute>n-1) < \<acute>run_len!(\<acute>n+1) 
      THEN 
        \<acute>n:==\<acute>n-1 
      FI
    ELSE 
      IF \<acute>n<0 \<or> \<acute>run_len!\<acute>n > \<acute>run_len!(\<acute>n+1) 
      THEN 
        THROW 
      FI
    FI;;
    CALL merge_at(\<acute>n) 
  OD 
CATCH SKIP END"

print_locale merge_collapse_impl

procedures (imports globals_var)
push_run(run_base_i::nat, run_len_i::nat)
"\<acute>run_base!\<acute>stack_size :== \<acute>run_base_i ;;
 \<acute>run_len!\<acute>stack_size :== \<acute>run_len_i ;;
 \<acute>stack_size :== \<acute>stack_size + 1"

procedures (imports globals_var)
merge_force_collapse()
where n::nat in
"WHILE \<acute>stack_size > 1 
DO
  \<acute>n :== \<acute>stack_size - 2;;
  IF (\<acute>n > 0 \<and> \<acute>run_len!(\<acute>n-1) < \<acute>run_len!(\<acute>n+1)) 
  THEN 
    \<acute>n:==\<acute>n - 1 
  FI;;
  CALL merge_at(\<acute>n) 
OD"

(* assume min_run = 16 *)
procedures (imports globals_var)
reverse_range(array::"int list", lo::nat, hi::nat| ret::"int list")
where t::int in
"
TRY
IF \<acute>hi = 0 THEN THROW ELSE (* to address the problem of natural number *)
\<acute>hi:==\<acute>hi-1;;
WHILE \<acute>lo < \<acute>hi DO
 \<acute>t:==\<acute>array!\<acute>lo;;
 \<acute>array!\<acute>lo :== \<acute>array!\<acute>hi;;
 \<acute>array!\<acute>hi :== \<acute>t;;
 \<acute>lo :== \<acute>lo+1;;
 \<acute>hi :== \<acute>hi-1
OD FI
CATCH Skip END;;
\<acute>ret :== \<acute>array"

procedures (imports globals_var)
count_run_and_make_ascending(array::"int list", lo::nat, hi::nat| ret_value::nat, ret::"int list")
where run_hi::nat in
"
\<acute>run_hi:==\<acute>lo+1;;
TRY
 IF \<acute>run_hi = \<acute>hi THEN \<acute>ret_value:==1;;\<acute>ret :== \<acute>array;;THROW FI;;
 IF \<acute>array!\<acute>run_hi < \<acute>array!\<acute>lo
 THEN
  \<acute>run_hi :== \<acute>run_hi+1;;
  WHILE (\<acute>run_hi < \<acute>hi & \<acute>array!\<acute>run_hi < \<acute>array!(\<acute>run_hi-1))
  DO \<acute>run_hi :== \<acute>run_hi+1 OD;;
  \<acute>array :== CALL reverse_range(\<acute>array, \<acute>lo, \<acute>run_hi)
 ELSE
  \<acute>run_hi :== \<acute>run_hi+1;;
  WHILE (\<acute>run_hi < \<acute>hi & \<acute>array!\<acute>run_hi \<ge> \<acute>array!(\<acute>run_hi-1))
  DO \<acute>run_hi :== \<acute>run_hi+1 OD
 FI;;
 \<acute>ret_value :== \<acute>run_hi - \<acute>lo;;
 \<acute>ret :== \<acute>array
CATCH Skip END"

procedures (imports globals_var)
binary_sort(array::"int list", lo::nat, hi::nat, start::nat| ret::"int list")
where pivot::int left::nat right::nat mid::nat move::nat in
"
IF \<acute>start = \<acute>lo THEN \<acute>start :== \<acute>start + 1 FI;;
WHILE \<acute>start < \<acute>hi DO
 \<acute>pivot :== \<acute>array!\<acute>start;;
 \<acute>left :== \<acute>lo;;
 \<acute>right :== \<acute>start;;
 WHILE \<acute>left < \<acute>right DO
  \<acute>mid :== (\<acute>left+\<acute>right) div 2;;
  IF \<acute>pivot < \<acute>array!\<acute>mid 
  THEN 
    \<acute>right :== \<acute>mid 
  ELSE 
    \<acute>left :== \<acute>mid+1 
  FI
 OD;;
 \<acute>move :== \<acute>start - \<acute>left;;
 \<acute>array :== list_copy \<acute>array (\<acute>left+1) \<acute>array \<acute>left \<acute>move;;
 \<acute>array!\<acute>left :== \<acute>pivot;;
 \<acute>start :== \<acute>start + 1
OD;;
\<acute>ret :== \<acute>array
"

procedures (imports globals_var)
sort(array::"int list", lo::nat, hi::nat| ret::"int list")
where min_run::nat n_remaining::nat run_len_i::nat force::nat init_run_len_i::nat in
"
TRY
\<acute>n_remaining :== \<acute>hi - \<acute>lo;;
IF (\<acute>n_remaining < 2) THEN \<acute>ret :== \<acute>array;; THROW FI;;
IF (\<acute>n_remaining < 32) THEN
   CALL count_run_and_make_ascending(\<acute>array, \<acute>lo, \<acute>hi, \<acute>init_run_len_i, \<acute>array);;(* return two values*)
  \<acute>array :== CALL binary_sort(\<acute>array, \<acute>lo, \<acute>hi, \<acute>lo+\<acute>init_run_len_i);;
  \<acute>ret :== \<acute>array;;
  THROW
FI;;
\<acute>a:==\<acute>array;;
\<acute>stack_size :== 0;;
\<acute>min_run :== 16;;
IF size \<acute>a < 120 THEN \<acute>stack_len :== 4 ELSE
IF size \<acute>a < 1542 THEN \<acute>stack_len :== 9 ELSE
IF size \<acute>a < 119151 THEN \<acute>stack_len :== 18 ELSE
\<acute>stack_len :== 39 FI FI FI;;
\<acute>run_len :== replicate \<acute>stack_len (0::nat);;
\<acute>run_base :== replicate \<acute>stack_len (0::nat);;
CALL count_run_and_make_ascending(\<acute>a, \<acute>lo, \<acute>hi, \<acute>run_len_i, \<acute>a);;
  IF \<acute>run_len_i < \<acute>min_run THEN
   IF \<acute>n_remaining \<le> \<acute>min_run THEN
    \<acute>force :== \<acute>n_remaining
   ELSE
    \<acute>force :== \<acute>min_run
   FI;;
   \<acute>a :== CALL binary_sort(\<acute>a, \<acute>lo, \<acute>lo+\<acute>force, \<acute>lo+\<acute>run_len_i);;
   \<acute>run_len_i :== \<acute>force
  FI;;
 CALL push_run(\<acute>lo, \<acute>run_len_i);;
 CALL merge_collapse();;
 \<acute>lo :== \<acute>lo + \<acute>run_len_i;;
 \<acute>n_remaining :== \<acute>n_remaining - \<acute>run_len_i;;
 WHILE \<acute>n_remaining \<noteq> 0 DO 
 CALL count_run_and_make_ascending(\<acute>a, \<acute>lo, \<acute>hi ,\<acute>run_len_i, \<acute>a);;
  IF \<acute>run_len_i < \<acute>min_run THEN
   IF \<acute>n_remaining \<le> \<acute>min_run THEN
    \<acute>force :== \<acute>n_remaining
   ELSE
    \<acute>force :== \<acute>min_run
   FI;;
   \<acute>a :== CALL binary_sort(\<acute>a, \<acute>lo, \<acute>lo+\<acute>force, \<acute>lo+\<acute>run_len_i);;
   \<acute>run_len_i :== \<acute>force
  FI;;
 CALL push_run(\<acute>lo, \<acute>run_len_i);;
 CALL merge_collapse();;
 \<acute>lo :== \<acute>lo + \<acute>run_len_i;;
 \<acute>n_remaining :== \<acute>n_remaining - \<acute>run_len_i
 OD;;
CALL merge_force_collapse();;
\<acute>ret:==\<acute>a
CATCH Skip END
"



end