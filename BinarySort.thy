theory BinarySort
  imports "../Simpl/Vcg" Main "~~/src/HOL/Library/Code_Target_Numeral" "TimSortLemma"
begin

definition sorted_in::"'a list \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"sorted_in xs c lo hi = (\<forall>i. (i\<ge>lo\<and>i<hi)\<longrightarrow> ((c (xs!i) (xs!(i+1))) \<le> 0))"

definition comp_has_tran::"('a \<Rightarrow> 'a \<Rightarrow> int) \<Rightarrow> bool" where
"comp_has_tran cmp = (\<forall>a b c. (cmp a b \<le> 0) \<and> ( cmp b c \<le> 0) \<longrightarrow> (cmp a c = cmp a b))"

lemma "comp_has_tran c \<Longrightarrow> c t r \<le> 0"

thm allE
value "sorted [0,-1::int]"
value "([0::int,-1]!0) \<le>([0::int,-1]!1)"

lemma sorted_in_conca:"sorted_in xs c lo mid \<and> sorted_in xs c mid hi \<Longrightarrow> sorted_in xs c lo hi"
  apply (auto simp add:sorted_in_def)
  using not_less by blast

lemma sorted_in_hi:"sorted_in xs c lo hi \<and> (c (xs!hi) (xs!(hi+1)) \<le>0) \<Longrightarrow> sorted_in xs c lo (hi+1)"
  apply (auto simp add:sorted_in_def)
  using less_antisym
  by blast 

lemma sorted_in_pick_two:"sorted_in xs cmp lo hi \<and> i\<ge>lo \<and> j\<le>hi \<and> i<j \<and> comp_has_tran cmp\<Longrightarrow> (cmp (xs!i) (xs!j)) \<le> 0"
  apply (simp add:sorted_in_def)
  apply (induct j arbitrary:xs lo hi i cmp)
   apply auto
  apply (case_tac "i=Suc j")
   apply simp
  apply (subgoal_tac "cmp (xs ! i) ( xs ! j) \<le> 0")

hoarestate 'a globals_var = 
 stack_size:: nat
 run_base :: "nat list"
 run_len :: "nat list"
 stack_len :: nat (* length of run_len *)
 a :: " 'a list" (* the array to be sorted *)
 comp :: " 'a \<Rightarrow> 'a \<Rightarrow> int"

hoarestate 'a binary_sort_locals_var = 'a globals_var +
 pivot :: 'a
 left :: nat
 right :: nat
 mid :: nat
 move :: nat
 lo :: nat
 hi :: nat
 start :: nat

print_locale binary_sort_locals_var

procedures (imports binary_sort_locals_var)
binary_sort(lo::nat, hi::nat, start::nat)
"
\<acute>start :== \<acute>left;;
IF \<acute>start = \<acute>lo THEN \<acute>start :== \<acute>start + 1 FI;;
WHILE \<acute>start < \<acute>hi DO
 \<acute>pivot :== \<acute>a!\<acute>start;;
 \<acute>left :== \<acute>lo;;
 \<acute>right :== \<acute>start;;
 WHILE \<acute>left < \<acute>right DO
  \<acute>mid :== (\<acute>left+\<acute>right) div 2;;
  IF (\<acute>comp \<acute>pivot (\<acute>a!\<acute>mid)) < 0 THEN \<acute>right :== \<acute>mid ELSE \<acute>left :== \<acute>mid+1 FI
 OD;;
 \<acute>move :== \<acute>start - \<acute>left;;
 \<acute>a :== (list_copy \<acute>a (\<acute>left+1) \<acute>a \<acute>left \<acute>move);;
 \<acute>a!\<acute>left :== \<acute>pivot;;
 \<acute>start :== \<acute>start + 1
OD
"

lemma (in binary_sort_impl) binary_sort_spec: 
"\<forall>\<sigma>. \<Gamma>\<turnstile> \<lbrace>\<sigma>. (\<acute>a \<noteq> []) \<and> (\<acute>lo \<ge> 0) \<and>
(\<acute>lo < \<acute>hi) \<and> (\<acute>hi \<le> size \<acute>a) \<and>
(\<acute>start \<le> \<acute>hi) \<and> (\<acute>lo \<le> \<acute>start) \<and>
(sorted_in \<acute>a \<acute>lo \<acute>start) \<rbrace>
PROC binary_sort(\<acute>lo, \<acute>hi, \<acute>start)
\<lbrace> 
(sorted_in \<acute>a \<^bsup>\<sigma>\<^esup>lo (\<^bsup>\<sigma>\<^esup>hi-1)) \<and>
(size \<acute>a = size \<^bsup>\<sigma>\<^esup>a) 
\<rbrace>
"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (hoare_rule anno="
            \<acute>stack_len :== \<acute>stack_len;; IF \<acute>start = \<acute>lo THEN \<acute>start :== \<acute>start + 1 FI;;
            WHILE \<acute>start < \<acute>hi 
            INV \<lbrace> \<acute>start\<ge>\<acute>lo \<and> \<acute>start\<le>\<acute>hi \<and>
                   size \<acute>array = size \<^bsup>\<sigma>\<^esup>array \<and> \<acute>hi \<le> size \<acute>array \<and>
                   (size \<acute>a = size \<^bsup>\<sigma>\<^esup>a) \<and> (sorted_in \<acute>array \<^bsup>\<sigma>\<^esup>lo (\<acute>start-1)) \<and> \<^bsup>\<sigma>\<^esup>lo = \<acute>lo \<and> \<^bsup>\<sigma>\<^esup>hi = \<acute>hi\<rbrace>
            DO \<acute>pivot :== \<acute>array ! \<acute>start;; \<acute>left :== \<acute>lo;; \<acute>right :== \<acute>start;;
               WHILE \<acute>left < \<acute>right 
               INV \<lbrace> \<acute>left\<ge>\<acute>lo \<and> \<acute>left\<le>\<acute>right \<and> \<acute>right\<le>\<acute>start \<and> 
                     \<acute>left\<le>(\<acute>right+\<acute>left) div 2 \<and> \<acute>right\<ge>(\<acute>right+\<acute>left) div 2 \<and>
                     \<acute>left \<le> size \<acute>array \<and> size \<acute>array = size \<^bsup>\<sigma>\<^esup>array \<and>
                     \<acute>start\<ge>\<acute>lo \<and> \<acute>start<\<acute>hi \<and>
                     \<acute>hi \<le> size \<acute>array \<and>
                     (size \<acute>a = size \<^bsup>\<sigma>\<^esup>a) \<and>
                     (sorted_in \<acute>array \<^bsup>\<sigma>\<^esup>lo (\<acute>start-1)) \<and>
                     (\<forall>i. (i\<ge>\<^bsup>\<sigma>\<^esup>lo\<and>i<\<acute>left)\<longrightarrow> \<acute>pivot\<ge>\<acute>array!i) \<and>
                     (\<forall>i. (i\<ge>\<acute>right \<and> i<\<acute>start) \<longrightarrow> \<acute>pivot<\<acute>array!i) \<and> \<^bsup>\<sigma>\<^esup>lo = \<acute>lo \<and> \<^bsup>\<sigma>\<^esup>hi = \<acute>hi\<rbrace>
               DO \<acute>mid :== (\<acute>left + \<acute>right) div 2;; IF \<acute>pivot < \<acute>array ! \<acute>mid THEN \<acute>right :== \<acute>mid ELSE \<acute>left :== \<acute>mid + 1 FI OD;;
               \<acute>move :== \<acute>start - \<acute>left;;
               \<acute>array :== (list_copy \<acute>array (\<acute>left+1) \<acute>array \<acute>left \<acute>move);;
               \<acute>array!\<acute>left :== \<acute>pivot;;
               \<acute>start :== \<acute>start + 1 
            OD" in HoarePartial.annotateI)
  apply vcg
      apply simp_all
(*      apply (intro conjI impI)
       apply (simp add:sorted_in_def)
      apply (simp add:sorted_in_def)
      apply auto[1]
     apply (intro conjI impI)
      apply linarith
       apply linarith
   apply (intro conjI impI)
             apply simp_all
     apply clarsimp
     apply (subgoal_tac "arraya ! ((left + right) div 2) \<le> arraya!i")
      apply linarith
  using sorted_in_pick_two
     apply (smt One_nat_def add.commute diff_Suc_1 le_add1 less_imp_Suc_add order_trans)
    apply (clarsimp)
    apply (subgoal_tac "arraya ! ((left + right) div 2) \<ge> arraya!i")
     apply linarith
    apply (case_tac " (left + right) div 2 = i")
     apply fastforce
    apply (subgoal_tac "(right + left) div 2 < start")
  using sorted_in_pick_two
     apply (metis One_nat_def add.commute diff_Suc_1 less_Suc_eq_le less_imp_Suc_add)
  using le_half
    apply linarith
   apply (subgoal_tac "length (list_copy arraya (Suc left) arraya left (start - left)) = length arraya")
    apply (intro impI conjI)
      apply simp+
    prefer 2
   apply (subgoal_tac "left=right")
    apply (case_tac "left=start")
     apply (simp add: list_copy_zero)
    apply (simp add: less_le list_copy_len)
   apply (simp_all)
  apply clarsimp
  apply (subgoal_tac "right=left")
   apply (clarsimp)
   prefer 2
   apply simp
  apply (clarsimp simp add:sorted_in_def list_copy_def)
  apply (case_tac "i<left-1")
   apply clarsimp
  apply (case_tac "i\<ge>left+1")
   apply (clarsimp simp del:length_take)
   apply (smt Suc_less_eq Suc_pred antisym_conv3 le_trans less_le less_nat_zero_code)
  apply (case_tac "i=left")
  apply (clarsimp simp del:length_take)
   apply (simp add: le_less)
  apply (case_tac "i+1=left")
   apply (clarsimp)
  apply (metis Suc_eq_plus1 Suc_pred diff_self_eq_0 less_antisym less_imp_diff_less not_less plus_nat.add_0)
  done *)
end




