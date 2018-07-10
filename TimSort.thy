theory TimSort
  imports "Simpl/Vcg" Main "~~/src/HOL/Library/Code_Target_Numeral" "TimSortLemma" "TimSortProc" "GallopA"
begin

definition equal_size :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
"equal_size a b = (size a = size b)"

definition invariant :: "nat list \<Rightarrow> nat list \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> bool" where 
"invariant run_len run_base a stack_size \<equiv> 
(size (run_base) = size (run_len)) \<and>
(size a < 120 \<longrightarrow>  size run_len = 4) \<and>
(size a \<ge> 120 \<and> size a < 1542 \<longrightarrow>  size run_len = 9) \<and>
(size a \<ge>1542 \<and> size a < 119151 \<longrightarrow>  size run_len = 18) \<and>
(size a \<ge> 119151 \<and> size a < 2917196496 \<longrightarrow>  size run_len = 39) \<and>
(size a < 2917196496) \<and>
(run_base!0 + (sumn run_len stack_size) \<le> size a) \<and>
(stack_size \<ge> 0) \<and> (stack_size \<le> size run_base) \<and>
(\<forall>i. ((i\<ge>5 \<and> i\<le>stack_size)\<longrightarrow>(elem_inv run_len (stack_size-i) 16))) \<and>
(stack_size \<ge>4 \<longrightarrow> elem_bigger_than_next run_len (stack_size-4)) \<and>
(stack_size \<ge>3 \<longrightarrow> elem_larger_than_bound run_len (stack_size-3) 16) \<and>
(stack_size \<ge>2 \<longrightarrow>elem_larger_than_bound run_len (stack_size-2) 16) \<and>
(stack_size \<ge>1 \<longrightarrow>elem_larger_than_bound run_len (stack_size-1) 1) \<and> 
(\<forall>i. ((i\<ge>0 \<and> i<stack_size-1)\<longrightarrow>(run_base!i + run_len!i = run_base!(i+1)))) \<and>
(elem_larger_than_bound run_base 0 0)"


lemma (in merge_at_impl) merge_at_spec: 
"\<forall>\<sigma>. \<Gamma>\<turnstile> \<lbrace>\<sigma>.
(\<acute>stack_size=2 \<longrightarrow> \<acute>i=\<acute>stack_size-2) \<and>
(\<acute>stack_size\<ge>3 \<longrightarrow> (\<acute>i=\<acute>stack_size-2 \<or>\<acute>i=\<acute>stack_size-3)) \<and>
(\<acute>stack_size > 1) \<and> (\<acute>i\<ge>0) \<and>
(\<acute>a \<noteq> []) \<and>
(invariant \<acute>run_len \<acute>run_base \<acute>a \<acute>stack_size) \<rbrace> 
  PROC merge_at(\<acute>i) 
\<lbrace> (\<acute>i = \<^bsup>\<sigma>\<^esup>i) \<and> (\<acute>run_base!0 = \<^bsup>\<sigma>\<^esup>run_base!0) \<and>
(size \<acute>a = size \<^bsup>\<sigma>\<^esup>a) \<and>
(\<acute>stack_size = \<^bsup>\<sigma>\<^esup>stack_size - 1) \<and>
(\<acute>run_len!\<acute>i = (\<^bsup>\<sigma>\<^esup>run_len)!(\<acute>i) + (\<^bsup>\<sigma>\<^esup>run_len!(\<acute>i+1))) \<and> 
((\<acute>i = \<^bsup>\<sigma>\<^esup>stack_size -3)\<longrightarrow>(\<acute>run_len!(\<acute>i+1) = \<^bsup>\<sigma>\<^esup>run_len!(\<acute>i+2)) \<and> (\<acute>run_base!(\<acute>i+1) = \<^bsup>\<sigma>\<^esup>run_base!(\<acute>i+2))) \<and>
(invariant \<acute>run_len \<acute>run_base \<acute>a \<acute>stack_size) \<and>
(sumn \<acute>run_len \<acute>stack_size = sumn \<^bsup>\<sigma>\<^esup>run_len \<^bsup>\<sigma>\<^esup>stack_size) \<and>
(\<acute>run_len!(\<acute>stack_size-1) \<ge> \<^bsup>\<sigma>\<^esup>run_len!(\<^bsup>\<sigma>\<^esup>stack_size-1)) \<rbrace>"
  apply (simp only:invariant_def)
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply vcg
  apply (rename_tac a ys xs l i)
  apply (case_tac "l=2")
   apply (subgoal_tac "sumn xs 2 = xs!0 + xs!1")
  prefer 2
  using sumn.simps numeral_2_eq_2
    apply (metis Nat.add_0_right One_nat_def add.commute)
   apply (clarsimp simp add: elem_inv_def elem_larger_than_bound_def elem_bigger_than_next_2_def elem_bigger_than_next_def)
   apply (subgoal_tac "length xs > 0")
    apply (clarsimp simp add:nth_list_update)
   apply force
(* finish the case of stack_size = 2 *)
  apply clarsimp
  apply (erule disjE)
   apply (subgoal_tac "i\<noteq>l-3")
    prefer 2 
    apply linarith
  apply clarsimp
   apply (intro conjI impI)
  apply (clarsimp simp add:elem_larger_than_bound_def)
     apply (metis diff_less less_Suc_eq_le less_antisym less_imp_diff_less not_gr_zero not_le not_numeral_le_zero)
  using run_len_iter
    apply (smt One_nat_def Suc_diff_Suc Suc_lessD leD leI le_add2 less_le_trans numeral_2_eq_2)
   apply (rule allI)
   apply (clarsimp simp add:elem_larger_than_bound_def elem_inv_def elem_bigger_than_next_2_def elem_bigger_than_next_def)
   apply (intro conjI impI)
              apply (metis Suc_leI numeral_2_eq_2 sumn1)
             apply linarith
            apply clarsimp
           apply (smt Suc_diff_Suc Suc_le_mono Suc_numeral Suc_pred le_imp_less_Suc le_less_trans less_imp_le_nat not_less_eq numeral_3_eq_3 semiring_norm(2) semiring_norm(8))
          apply (metis (no_types) numeral_3_eq_3)
         apply (metis Suc_diff_Suc Suc_lessD leD minus_nat.diff_0 not_less_eq nth_list_update_eq numeral_2_eq_2 trans_le_add2)
  using sumn1
        apply (metis Suc_leI numeral_2_eq_2)
       apply (metis Suc_diff_Suc Suc_eq_plus1 diff_zero discrete le_add2 less_or_eq_imp_le nth_list_update_eq numeral_2_eq_2)
      apply (metis Suc_diff_Suc diff_zero gr0I leD not_less_eq numeral_2_eq_2)
     apply (metis Suc_diff_Suc leD less_le minus_nat.diff_0 not_less_eq numeral_2_eq_2)
  using run_len_iter
    apply (metis One_nat_def Suc_diff_Suc Suc_lessD add.commute numeral_2_eq_2)
(* finish the first 1/3 of i=stack_size - 2 *)
   apply (rule allI)
   apply clarsimp
   apply (intro conjI impI)
  using sumn1
                   apply (metis One_nat_def Suc_1 Suc_leI)
                  apply linarith
                 apply clarsimp
                apply clarsimp
                apply (smt Suc_diff_Suc Suc_le_mono Suc_numeral Suc_pred le_imp_less_Suc le_less_trans less_imp_le_nat not_less_eq numeral_3_eq_3 semiring_norm(2) semiring_norm(8))
               apply (metis numeral_3_eq_3)
              apply (metis Suc_diff_Suc Suc_lessD leD minus_nat.diff_0 not_less_eq nth_list_update_eq numeral_2_eq_2 trans_le_add2)
  using Suc_leI numeral_2_eq_2 sumn1 apply presburger
            apply (metis Suc_diff_Suc Suc_eq_plus1 diff_zero discrete le_add2 less_or_eq_imp_le nth_list_update_eq numeral_2_eq_2)
  apply (subgoal_tac "ys ! Suc (l - 2) + xs!Suc(l-2) \<le> length a")
            apply linarith
  using run_len_iter
           apply (metis One_nat_def Suc_diff_Suc Suc_lessD add.commute numeral_2_eq_2)
  using Suc_leI numeral_2_eq_2 sumn1 apply presburger
         apply linarith
        apply clarsimp
       apply clarsimp
       apply (smt Suc_diff_Suc Suc_le_mono Suc_less_eq Suc_numeral le_imp_less_Suc le_less_trans less_imp_le_nat minus_nat.diff_0 numeral_3_eq_3 semiring_norm(2) semiring_norm(8))
      apply (metis numeral_3_eq_3)
     apply (metis Suc_leI add_gr_0 less_le_trans nth_list_update_eq numeral_2_eq_2)
  using Suc_leI numeral_2_eq_2 sumn1 apply presburger
   apply (metis Suc_diff_Suc Suc_eq_plus1 diff_zero discrete le_add2 less_or_eq_imp_le nth_list_update_eq numeral_2_eq_2)
(* finish the case of i = stack_size -2 *)
  apply (clarsimp)
  apply (intro conjI)
  apply (clarsimp simp add:elem_larger_than_bound_def)
    apply (metis Suc_lessD diff_Suc_less gr0I le_less less_imp_diff_less not_numeral_le_zero numeral_3_eq_3)
  apply (subgoal_tac "ys ! Suc (l - 2) \<le> length a")
    apply (metis Suc_diff_Suc Suc_lessI le_antisym lessI nat_le_linear numeral_2_eq_2 numeral_3_eq_3 trans_le_add1)
  using run_len_iter
   apply (smt One_nat_def Suc_diff_Suc Suc_lessD leD leI le_add2 less_le_trans numeral_2_eq_2)
  apply (rule allI)
  apply (clarsimp simp add:elem_larger_than_bound_def elem_inv_def elem_bigger_than_next_2_def elem_bigger_than_next_def)
  apply (intro conjI impI)
  using sumn2
              apply (metis Suc_leI Suc_lessI numeral_2_eq_2 numeral_3_eq_3)
             apply linarith
            apply clarsimp
           apply clarsimp
           apply (smt Suc_diff_Suc Suc_le_mono Suc_numeral Suc_pred le_imp_less_Suc le_less_trans less_imp_le_nat not_less_eq numeral_3_eq_3 semiring_norm(2) semiring_norm(8))
          apply (metis nth_list_update_eq numeral_3_eq_3 trans_le_add1)
         apply clarsimp
         apply (smt One_nat_def Suc_diff_Suc Suc_eq_plus1_left Suc_lessD Suc_lessI leD length_list_update minus_nat.diff_0 not_less_eq nth_list_update_eq numeral_3_eq_3 one_add_one)
        apply clarsimp
        apply (case_tac "i=l-3")
         apply clarsimp
         apply (metis Suc_diff_Suc Suc_mono ab_semigroup_add_class.add_ac(1) less_SucI)
        apply clarsimp
  using sumn2
       apply (metis Suc_leI Suc_lessI eval_nat_numeral(3) numeral_2_eq_2)
      apply clarsimp
      apply (smt Suc_diff_Suc Suc_lessI leD length_list_update less_or_eq_imp_le minus_nat.diff_0 not_less_eq nth_list_update_eq numeral_2_eq_2 numeral_3_eq_3)
     apply (smt Suc_diff_Suc Suc_lessD Suc_pred gr0I leD not_less_eq not_numeral_le_zero numeral_2_eq_2 numeral_3_eq_3)
  apply (subgoal_tac "length xs > l-2" "Suc(l-3) = l-2")
      apply (metis (no_types) diff_less less_le_trans numeral_1_eq_Suc_0 zero_less_numeral)
     apply linarith
    apply linarith
  using run_len_iter
   apply (smt One_nat_def Suc_diff_Suc Suc_lessD Suc_lessI leD leI le_add2 less_le_trans numeral_2_eq_2 numeral_3_eq_3)
  apply (rule allI)
  apply (intro conjI impI)
  using sumn2 apply(simp_all)
              apply clarsimp
             apply clarsimp
             apply (smt Suc_diff_Suc Suc_le_mono Suc_numeral le_imp_less_Suc le_less_trans less_imp_le_nat minus_nat.diff_0 not_less_eq numeral_3_eq_3 semiring_norm(2) semiring_norm(8))
            apply (metis nth_list_update_eq numeral_3_eq_3 trans_le_add1)
           apply clarsimp
           apply (smt One_nat_def Suc_diff_Suc Suc_eq_plus1_left Suc_lessD Suc_lessI leD length_list_update minus_nat.diff_0 not_less_eq nth_list_update_eq numeral_3_eq_3 one_add_one)
          apply clarsimp
          apply (case_tac "i=l-3")
           apply clarsimp
           apply (metis Suc_diff_Suc Suc_mono ab_semigroup_add_class.add_ac(1) less_SucI)
          apply clarsimp
         apply (smt Suc_diff_Suc Suc_lessI leD length_list_update less_or_eq_imp_le minus_nat.diff_0 not_less_eq nth_list_update_eq numeral_2_eq_2 numeral_3_eq_3)
        apply(subgoal_tac "ys ! Suc (l - 3) + xs!Suc(l-3) \<le> length a")
         apply linarith
  using run_len_iter
        apply (smt One_nat_def Suc_diff_Suc Suc_lessD Suc_lessI leD leI le_add2 lessI less_le_trans numeral_2_eq_2 numeral_3_eq_3)
       apply clarsimp
      apply clarsimp
      apply (smt Suc_diff_Suc Suc_le_mono Suc_numeral le_imp_less_Suc le_less_trans less_imp_le_nat minus_nat.diff_0 not_less_eq numeral_3_eq_3 semiring_norm(2) semiring_norm(8))
     apply (metis nth_list_update_eq numeral_3_eq_3 trans_le_add1)
    apply clarsimp
    apply (smt One_nat_def Suc_diff_Suc Suc_eq_plus1_left Suc_lessD Suc_lessI leD length_list_update minus_nat.diff_0 not_less_eq nth_list_update_eq numeral_3_eq_3 one_add_one)
   apply clarsimp
   apply (case_tac "i=l-3")
    apply clarsimp
    apply (metis Suc_diff_Suc Suc_mono ab_semigroup_add_class.add_ac(1) less_SucI)
   apply clarsimp
  apply clarsimp
  apply (smt Suc_diff_Suc Suc_lessI leD length_list_update less_or_eq_imp_le minus_nat.diff_0 not_less_eq nth_list_update_eq numeral_2_eq_2 numeral_3_eq_3)
  done  


lemma (in push_run_impl) push_run_spec:
"\<forall>\<sigma>. \<Gamma>\<turnstile> \<lbrace>\<sigma>. 
(\<acute>run_len_i>0)\<and>(\<acute>run_len_i\<le>size \<acute>a)\<and>(\<acute>run_base_i\<ge>0)\<and>
(\<acute>stack_size>0 \<longrightarrow> (\<acute>run_base_i=\<acute>run_base!(\<acute>stack_size-1)+\<acute>run_len!(\<acute>stack_size-1))) \<and>
(\<acute>run_len_i+\<acute>run_base_i \<le> size \<acute>a) \<and>
(\<forall>i. ((i\<ge>3 \<and> i\<le>\<acute>stack_size)\<longrightarrow>(elem_inv \<acute>run_len (\<acute>stack_size-i) 16))) \<and>
(\<acute>stack_size\<ge>2 \<longrightarrow> elem_bigger_than_next \<acute>run_len (\<acute>stack_size-2)) \<and>
(\<acute>stack_size\<ge>1 \<longrightarrow> elem_larger_than_bound \<acute>run_len (\<acute>stack_size-1) 16) \<and>
(\<acute>stack_size\<ge>0 \<and> \<acute>stack_size\<le>(size \<acute>run_len)) \<and>
(invariant \<acute>run_len \<acute>run_base \<acute>a \<acute>stack_size)
 \<rbrace>
PROC push_run(\<acute>run_base_i, \<acute>run_len_i) 
\<lbrace> (\<acute>run_base!(\<^bsup>\<sigma>\<^esup>stack_size) = \<acute>run_base_i) \<and>
(\<acute>run_len!( \<^bsup>\<sigma>\<^esup>stack_size) = \<acute>run_len_i) \<and>
(\<acute>stack_size =  \<^bsup>\<sigma>\<^esup>stack_size + 1) \<and>
(\<acute>run_base_i = \<^bsup>\<sigma>\<^esup>run_base_i) \<and>
(\<acute>run_len_i = \<^bsup>\<sigma>\<^esup>run_len_i) \<and>
(\<forall>i. (i\<ge>0 \<and> i<\<acute>stack_size-1) \<longrightarrow> (\<acute>run_len!i = \<^bsup>\<sigma>\<^esup>run_len!i)) \<and>
(\<forall>i. (i\<ge>0 \<and> i<\<acute>stack_size-1) \<longrightarrow> (\<acute>run_base!i = \<^bsup>\<sigma>\<^esup>run_base!i)) \<and> 
(invariant \<acute>run_len \<acute>run_base \<acute>a \<acute>stack_size) \<and>
(size \<acute>a = size \<^bsup>\<sigma>\<^esup>a) \<rbrace>"
  apply (simp add:invariant_def)
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply vcg
  apply (subgoal_tac "stack_size<length run_len")
   apply (rename_tac a ys xs l bi li)
   apply (simp add: elem_inv_def elem_larger_than_bound_def elem_bigger_than_next_2_def elem_bigger_than_next_def)
   apply (intro conjI impI)
  using sumn_update_no_use apply simp
     apply (case_tac "l=0")
      apply simp
     apply simp
     apply (subgoal_tac "ys!0 + sumn xs l = xs!(l-1) + ys!(l-1)")
      apply simp
  using run_len_iter apply simp
    apply clarsimp
    apply(drule_tac x="i-1" in spec)
    apply clarsimp
    apply (metis Suc_le_mono Suc_numeral Suc_pred diff_is_0_eq' eval_nat_numeral(3) le_SucI less_imp_diff_less less_than semiring_norm(2) semiring_norm(8) zero_less_numeral)
   apply clarsimp
   apply (smt One_nat_def Suc_le_eq Suc_lessI Suc_pred diff_Suc_1 less_nat_zero_code not_less nth_list_update_eq nth_list_update_neq)
(* lemma stack_never_overflow *)
  apply (rename_tac a rb rl l rbi rli)
  apply (subgoal_tac "l \<le> length rl")
  prefer 2
   apply simp
  apply (subgoal_tac "l \<noteq> length rl")
   apply simp
  apply clarsimp
  apply (subgoal_tac "rl \<noteq> []")
   prefer 2
   apply force
  apply (simp add: elem_inv_def)
  apply (case_tac "length a < 120")
  prefer 2
   apply (case_tac "length a < 1542")
    prefer 2
  apply (case_tac "length a < 119151")
     apply (simp_all add: elem_bigger_than_next_2_def elem_bigger_than_next_def elem_larger_than_bound_def)
     prefer 2
     prefer 2
     prefer 3
     prefer 4

     apply (subgoal_tac "119 \<le> sumn rl 4")
      prefer 2
  using rl_sum_lower_bound[of 4 _ 16, simplified] apply blast
       apply (subgoal_tac "rb ! 3 + rl ! 3 = rb ! 0 + sumn rl 4")
      prefer 2
  using run_len_iter[of 4] apply simp
     apply linarith

    apply (subgoal_tac "1541 \<le> sumn rl 9")
     prefer 2
  using rl_sum_lower_bound[of 9 _ 16, simplified] apply blast
       apply (subgoal_tac "rb ! 8 + rl ! 8 = rb ! 0 + sumn rl 9")
      prefer 2
  using run_len_iter[of 9] apply simp
    apply linarith

   apply (subgoal_tac "119150 \<le> sumn rl 18")
     prefer 2
  using rl_sum_lower_bound[of 18 _ 16, simplified] apply blast
       apply (subgoal_tac "rb ! 17 + rl ! 17 = rb ! 0 + sumn rl 18")
      prefer 2
  using run_len_iter[of 18] apply simp
   apply linarith

  apply (subgoal_tac "2917196495 \<le> sumn rl 39")
     prefer 2
  using rl_sum_lower_bound[of 39 _ 16, simplified] apply blast
       apply (subgoal_tac "rb ! 38 + rl ! 38 = rb ! 0 + sumn rl 39")
      prefer 2
  using run_len_iter[of 39] apply simp
  apply linarith
  done 

lemma (in merge_collapse_impl) merge_collapse_spec:
"\<forall>\<sigma>. \<Gamma>\<turnstile> \<lbrace>\<sigma>. (\<acute>stack_size>0) \<and> (\<acute>stack_size\<ge>4 \<longrightarrow> elem_inv \<acute>run_len (\<acute>stack_size-4) 16) \<and>
(\<acute>stack_size\<ge>3 \<longrightarrow> elem_bigger_than_next \<acute>run_len (\<acute>stack_size-3)) \<and>
(\<acute>a \<noteq> []) \<and>
(invariant \<acute>run_len \<acute>run_base \<acute>a \<acute>stack_size) \<rbrace>
PROC merge_collapse() 
\<lbrace> (\<forall>i. ((i\<ge>3 \<and> i\<le>\<acute>stack_size)\<longrightarrow>(elem_inv \<acute>run_len (\<acute>stack_size-i) 16))) \<and>
(\<acute>stack_size\<ge>2 \<longrightarrow> elem_bigger_than_next \<acute>run_len (\<acute>stack_size-2)) \<and>
(sumn \<acute>run_len \<acute>stack_size = sumn \<^bsup>\<sigma>\<^esup>run_len \<^bsup>\<sigma>\<^esup>stack_size ) \<and>
(\<acute>run_len!(\<acute>stack_size-1) \<ge> \<^bsup>\<sigma>\<^esup>run_len!(\<^bsup>\<sigma>\<^esup>stack_size-1)) \<and>
(\<acute>stack_size>0 \<and> \<acute>stack_size \<le> \<^bsup>\<sigma>\<^esup>stack_size) \<and>
(invariant \<acute>run_len \<acute>run_base \<acute>a \<acute>stack_size) \<and>
(size \<acute>a = size \<^bsup>\<sigma>\<^esup>a)\<and>
(\<acute>run_base!0 = \<^bsup>\<sigma>\<^esup>run_base!0) \<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (hoare_rule anno="TRY WHILE \<acute>stack_size > 1 
    INV \<lbrace>
    (sumn \<acute>run_len \<acute>stack_size  = sumn \<^bsup>\<sigma>\<^esup>run_len \<^bsup>\<sigma>\<^esup>stack_size) \<and>
    (\<forall>i. ((i\<ge>5 \<and> i\<le>\<acute>stack_size)\<longrightarrow>(elem_inv \<acute>run_len (\<acute>stack_size-i) 16))) \<and>
    (\<acute>stack_size \<ge>4 \<longrightarrow> elem_bigger_than_next \<acute>run_len (\<acute>stack_size-4)) \<and>
    (\<acute>stack_size \<ge>3 \<longrightarrow> elem_larger_than_bound \<acute>run_len (\<acute>stack_size-3) 16) \<and>
    (\<acute>stack_size \<ge>2 \<longrightarrow>elem_larger_than_bound \<acute>run_len (\<acute>stack_size-2) 16) \<and>
    (\<acute>stack_size \<ge>1 \<longrightarrow>elem_larger_than_bound \<acute>run_len (\<acute>stack_size-1) 1) \<and> 
    (\<forall>i. ((i\<ge>0 \<and> i<\<acute>stack_size-1)\<longrightarrow>(\<acute>run_base!i + \<acute>run_len!i = \<acute>run_base!(i+1)))) \<and>
    (\<acute>run_len!(\<acute>stack_size-1) \<ge> \<^bsup>\<sigma>\<^esup>run_len!(\<^bsup>\<sigma>\<^esup>stack_size-1)) \<and>
    (\<acute>stack_size>0 \<and> \<acute>stack_size \<le> \<^bsup>\<sigma>\<^esup>stack_size) \<and>
    (* add from class invariant *)
    (elem_larger_than_bound \<acute>run_base 0 0) \<and>
    (size \<acute>run_base = size \<acute>run_len) \<and>
    (\<acute>stack_size\<ge>0 \<and> \<acute>stack_size\<le>(size \<acute>run_len)) \<and>
    (size \<acute>a < 120 \<longrightarrow>  size \<acute>run_len = 4) \<and>
    (size \<acute>a \<ge> 120 \<and> size \<acute>a < 1542 \<longrightarrow>  size \<acute>run_len = 9) \<and>
    (size \<acute>a \<ge>1542 \<and> size \<acute>a < 119151 \<longrightarrow>  size \<acute>run_len = 18) \<and>
    (size \<acute>a \<ge> 119151 \<and> size \<acute>a < 2917196496\<longrightarrow>  size \<acute>run_len = 39) \<and>
    (size \<acute>a < 2917196496) \<and>
    (\<acute>run_base!0 + (sumn \<acute>run_len \<acute>stack_size) \<le> size \<acute>a) \<and>
    (* add from class invariant *)
      (size \<acute>a =  size \<^bsup>\<sigma>\<^esup>a)\<and> (\<^bsup>\<sigma>\<^esup>a\<noteq>[]) \<and> (* a \<noteq> [] is redundant actually but without make it clear you have to prove it *)
      (\<acute>run_base!0 = \<^bsup>\<sigma>\<^esup>run_base!0) \<rbrace>
    DO \<acute>n :== \<acute>stack_size-2;;
    IF (\<acute>n>0 \<and> \<acute>run_len!(\<acute>n-1) \<le> \<acute>run_len!\<acute>n + \<acute>run_len!(\<acute>n+1))
    \<or> (\<acute>n>1 \<and> \<acute>run_len!(\<acute>n-2) \<le> \<acute>run_len!(\<acute>n-1) + \<acute>run_len!\<acute>n)
    THEN IF \<acute>run_len!(\<acute>n-1) < \<acute>run_len!(\<acute>n+1) THEN \<acute>n:==\<acute>n-1 FI
    ELSE IF \<acute>n<0 \<or> \<acute>run_len!\<acute>n > \<acute>run_len!(\<acute>n+1) THEN THROW FI
    FI;;
    CALL merge_at(\<acute>n) OD CATCH SKIP END"
 in HoarePartial.annotateI)
  apply vcg
  apply (simp_all only:invariant_def)
    apply clarsimp
  prefer 2
   apply clarsimp
  apply (simp)
  apply (rename_tac xs l a ys xsn ln)
  apply (intro conjI impI allI)
             apply simp_all
        apply force
       apply force
      apply force
     apply force
    prefer 3
    apply force
   apply (simp_all add: elem_inv_def elem_bigger_than_next_2_def elem_bigger_than_next_def)
     apply (erule_tac conjE)
     apply (erule_tac conjE)
     apply (case_tac "i\<ge>5")
      apply (blast)
     apply (subgoal_tac "i=3\<or>i=4")
      prefer 2
      apply (metis Suc_numeral eval_nat_numeral(3) le_less_Suc_eq not_less semiring_norm(2) semiring_norm(8))
     apply (erule disjE)
      apply (clarsimp)
      apply (rule conjI)
       apply (metis Suc_diff_le diff_Suc_Suc not_less numeral_2_eq_2 numeral_3_eq_3)
      apply (metis Suc_diff_le diff_Suc_Suc not_less numeral_2_eq_2 numeral_3_eq_3 trans_le_add1)
     apply (rule conjI)
   apply (smt Suc_diff_le Suc_numeral diff_Suc_Suc nat_less_le not_less numeral_2_eq_2 numeral_3_eq_3 semiring_norm(2) semiring_norm(8) zero_less_Suc zero_less_diff)
  apply (simp add:elem_larger_than_bound_def)
     apply (smt Suc_diff_le Suc_lessI Suc_numeral diff_Suc_Suc diff_le_self diff_less le_antisym le_less_trans less_imp_le_nat semiring_norm(2) semiring_norm(8) zero_less_Suc zero_less_numeral)
  done 


lemma (in merge_force_collapse_impl) merge_force_collapse_spec:
"\<forall>\<sigma>. \<Gamma>\<turnstile> \<lbrace>\<sigma>. (\<acute>stack_size > 0) \<and>
(\<acute>a \<noteq> []) \<and>
(invariant \<acute>run_len \<acute>run_base \<acute>a \<acute>stack_size) \<rbrace>
PROC merge_force_collapse()
\<lbrace> (\<acute>stack_size = 1) \<and>
(invariant \<acute>run_len \<acute>run_base \<acute>a \<acute>stack_size) \<and>
(size \<acute>a = size \<^bsup>\<sigma>\<^esup>a) \<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (hoare_rule anno="WHILE \<acute>stack_size > 1
INV \<lbrace> (sumn \<acute>run_len \<acute>stack_size  = sumn \<^bsup>\<sigma>\<^esup>run_len \<^bsup>\<sigma>\<^esup>stack_size) \<and>
    (\<forall>i. ((i\<ge>5 \<and> i\<le>\<acute>stack_size)\<longrightarrow>(elem_inv \<acute>run_len (\<acute>stack_size-i) 16))) \<and>
    (\<acute>stack_size \<ge>4 \<longrightarrow> elem_bigger_than_next \<acute>run_len (\<acute>stack_size-4)) \<and>
    (\<acute>stack_size \<ge>3 \<longrightarrow> elem_larger_than_bound \<acute>run_len (\<acute>stack_size-3) 16) \<and>
    (\<acute>stack_size \<ge>2 \<longrightarrow>elem_larger_than_bound \<acute>run_len (\<acute>stack_size-2) 16) \<and>
    (\<acute>stack_size \<ge>1 \<longrightarrow>elem_larger_than_bound \<acute>run_len (\<acute>stack_size-1) 1) \<and> 
    (\<forall>i. ((i\<ge>0 \<and> i<\<acute>stack_size-1)\<longrightarrow>(\<acute>run_base!i + \<acute>run_len!i = \<acute>run_base!(i+1)))) \<and>
    (\<acute>run_len!(\<acute>stack_size-1) \<ge> \<^bsup>\<sigma>\<^esup>run_len!(\<^bsup>\<sigma>\<^esup>stack_size-1)) \<and>
    (\<acute>stack_size>0 \<and> \<acute>stack_size \<le> \<^bsup>\<sigma>\<^esup>stack_size) \<and>
    (* add from class invariant *)
    (elem_larger_than_bound \<acute>run_base 0 0) \<and>
    (size \<acute>run_base = size \<acute>run_len) \<and>
    (\<acute>stack_size\<ge>0 \<and> \<acute>stack_size\<le>(size \<acute>run_len)) \<and>
    (size \<acute>a < 120 \<longrightarrow>  size \<acute>run_len = 4) \<and>
    (size \<acute>a \<ge> 120 \<and> size \<acute>a < 1542 \<longrightarrow>  size \<acute>run_len = 9) \<and>
    (size \<acute>a \<ge>1542 \<and> size \<acute>a < 119151 \<longrightarrow>  size \<acute>run_len = 18) \<and>
    (size \<acute>a \<ge> 119151 \<and> size \<acute>a < 2917196496\<longrightarrow>  size \<acute>run_len = 39) \<and>
    (size \<acute>a < 2917196496) \<and>
    (\<acute>run_base!0 + (sumn \<acute>run_len \<acute>stack_size) \<le> size \<acute>a)
    (* add from class invariant *) \<and>
    (elem_larger_than_bound \<acute>run_base 0 0) \<and>
    (size \<acute>a = size \<^bsup>\<sigma>\<^esup>a) \<and> (\<^bsup>\<sigma>\<^esup>a\<noteq>[])\<rbrace>
DO \<acute>n :== \<acute>stack_size - 2;;
IF (\<acute>n > 0 \<and> \<acute>run_len!(\<acute>n-1) < \<acute>run_len!(\<acute>n+1)) THEN \<acute>n:==\<acute>n - 1 FI;;
CALL merge_at(\<acute>n) OD" in HoarePartial.annotateI)
  apply vcg
  apply (simp_all only:invariant_def)
    apply clarsimp
   prefer 2
   apply clarsimp
  apply clarsimp
  apply (intro conjI impI)
     apply force
    apply auto[1]
   apply force
  apply auto[1]
  done

lemma (in reverse_range_impl) reverse_range_modifies:
  shows
  "\<forall> \<sigma>. \<Gamma>\<turnstile> {\<sigma>} PROC reverse_range(\<acute>array, \<acute>lo, \<acute>hi, \<acute>ret)
            {t. t may_only_modify_globals \<sigma> in []}"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply (vcg spec=modifies)
  done

lemma (in reverse_range_impl) reverse_range_spec:
"\<forall>\<sigma>. \<Gamma>\<turnstile> \<lbrace>\<sigma>. (\<acute>array \<noteq> []) \<and>(\<acute>lo \<ge> 0) \<and>
(\<acute>lo \<le> \<acute>hi) \<and> (\<acute>hi \<le> size \<acute>array) \<rbrace>
PROC reverse_range(\<acute>array, \<acute>lo, \<acute>hi, \<acute>ret)
\<lbrace> (size \<acute>ret = size \<^bsup>\<sigma>\<^esup>array) \<rbrace>
"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (hoare_rule anno= "TRY
            IF \<acute>hi = 0 THEN THROW ELSE \<acute>hi :== \<acute>hi - 1;;
            WHILE \<acute>lo < \<acute>hi 
            INV \<lbrace>  
            (\<^bsup>\<sigma>\<^esup>lo \<le> \<acute>lo) \<and> (\<^bsup>\<sigma>\<^esup>hi > \<acute>hi) \<and> (\<acute>lo \<le> \<acute>hi + 1) \<and>
            (\<acute>lo - \<^bsup>\<sigma>\<^esup>lo = \<^bsup>\<sigma>\<^esup>hi - 1 - \<acute>hi) \<and>
            ( \<forall>i. i\<ge>\<^bsup>\<sigma>\<^esup>lo \<and> i<\<acute>lo \<longrightarrow> \<acute>array!i = \<^bsup>\<sigma>\<^esup>array!(\<^bsup>\<sigma>\<^esup>lo+\<^bsup>\<sigma>\<^esup>hi-i-1)) \<and>
            ( \<forall>i. i<\<^bsup>\<sigma>\<^esup>hi \<and> i>\<acute>hi \<longrightarrow> \<acute>array!i = \<^bsup>\<sigma>\<^esup>array!(\<^bsup>\<sigma>\<^esup>lo+\<^bsup>\<sigma>\<^esup>hi-i-1)) \<and>
            ( \<forall>i. i\<ge>\<acute>lo \<and> i\<le>\<acute>hi  \<longrightarrow> \<acute>array!i = \<^bsup>\<sigma>\<^esup>array!(i) ) \<and>
            (size \<acute>array = size \<^bsup>\<sigma>\<^esup>array) \<and>
            (\<^bsup>\<sigma>\<^esup>hi \<le> size \<^bsup>\<sigma>\<^esup>array)
            \<rbrace>
            DO \<acute>t :== \<acute>array ! \<acute>lo;; \<acute>array ! \<acute>lo :== \<acute>array ! \<acute>hi;;
               \<acute>array ! \<acute>hi :== \<acute>t;; \<acute>lo :== \<acute>lo + 1;;
               \<acute>hi :== \<acute>hi - 1 
            OD FI CATCH Skip END;;
           \<acute>ret :== \<acute>array" in HoarePartial.annotateI)
  apply vcg
    apply simp
  apply linarith
    apply (intro conjI impI allI)
        apply simp_all
     apply (case_tac "i=loa")
      apply simp
      apply (metis Suc_diff_Suc add.commute add_diff_cancel_right' diff_Suc_diff_eq1 le_add_diff_inverse nat_less_le)
     apply simp
    apply (case_tac "i=loa")
     apply clarify
  using neq0_conv apply linarith
    apply (case_tac "i=hia")
     apply clarsimp
     apply (metis Nat.add_diff_assoc Suc_leI le_add_diff_inverse)
   apply clarsimp
  apply clarsimp
  done


lemma (in binary_sort_impl) binary_sort_modifies:
  shows
  "\<forall> \<sigma>. \<Gamma>\<turnstile> {\<sigma>} PROC binary_sort(\<acute>array, \<acute>lo, \<acute>hi, \<acute>start, \<acute>ret)
            {t. t may_only_modify_globals \<sigma> in []}"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply (vcg spec=modifies)
  done

print_locale binary_sort_impl
lemma (in binary_sort_impl) binary_sort_spec: 
"\<forall>\<sigma>. \<Gamma>\<turnstile> \<lbrace>\<sigma>. (\<acute>array \<noteq> []) \<and> (\<acute>lo \<ge> 0) \<and>
(\<acute>lo < \<acute>hi) \<and> (\<acute>hi \<le> size \<acute>array) \<and>
(\<acute>start \<le> \<acute>hi) \<and> (\<acute>lo \<le> \<acute>start)  \<rbrace>
PROC binary_sort(\<acute>array, \<acute>lo, \<acute>hi, \<acute>start, \<acute>ret)
\<lbrace> 
(size \<acute>ret = size \<^bsup>\<sigma>\<^esup>array)  (* these variables are not modified by the procedure, so the class invariant holds *)
\<rbrace>
"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (hoare_rule anno="
IF \<acute>start = \<acute>lo THEN \<acute>start :== \<acute>start + 1 FI;;
WHILE \<acute>start < \<acute>hi 
 INV \<lbrace> \<acute>start\<ge>\<acute>lo \<and> \<acute>start\<le>\<acute>hi \<and>
       size \<acute>array = size \<^bsup>\<sigma>\<^esup>array \<and> \<acute>hi \<le> size \<acute>array \<rbrace>
 DO
 \<acute>pivot :== \<acute>array!\<acute>start;;
 \<acute>left :== \<acute>lo;;
 \<acute>right :== \<acute>start;;
 WHILE \<acute>left < \<acute>right
 INV \<lbrace> \<acute>left\<ge>0 \<and> \<acute>left\<le>\<acute>right \<and> \<acute>right\<le>\<acute>start \<and> 
       \<acute>left\<le>(\<acute>right+\<acute>left) div 2 \<and> \<acute>right\<ge>(\<acute>right+\<acute>left) div 2 \<and>
       \<acute>left \<le> size \<acute>array \<and> size \<acute>array = size \<^bsup>\<sigma>\<^esup>array \<and>
       \<acute>start\<ge>\<acute>lo \<and> \<acute>start<\<acute>hi \<and>
       \<acute>hi \<le> size \<acute>array  \<rbrace>
 DO
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
\<acute>ret :== \<acute>array" in HoarePartial.annotateI)
  apply vcg
  apply auto
  done

lemma (in count_run_and_make_ascending_impl) count_run_and_make_ascending_modifies:
  shows
  "\<forall> \<sigma>. \<Gamma>\<turnstile> {\<sigma>} PROC count_run_and_make_ascending(\<acute>array, \<acute>lo, \<acute>hi, \<acute>ret_value, \<acute>ret)
            {t. t may_only_modify_globals \<sigma> in []}"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply (vcg spec=modifies)
  done

lemma (in count_run_and_make_ascending_impl) count_run_and_make_ascending_spec:
"\<forall>\<sigma>. \<Gamma>\<turnstile> \<lbrace>\<sigma>. (\<acute>array \<noteq> []) \<and> (\<acute>lo \<ge> 0) \<and>
(\<acute>lo < \<acute>hi) \<and> (\<acute>hi \<le> size \<acute>array) \<rbrace>
PROC count_run_and_make_ascending(\<acute>array, \<acute>lo, \<acute>hi, \<acute>ret_value, \<acute>ret)
\<lbrace> (\<acute>ret_value \<ge> 0 \<and> \<acute>ret_value \<le> \<^bsup>\<sigma>\<^esup>hi - \<^bsup>\<sigma>\<^esup>lo) \<and>
(size \<acute>ret = size \<^bsup>\<sigma>\<^esup>array) 
\<rbrace>
"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (hoare_rule anno=" \<acute>run_hi :== \<acute>lo + 1;;
            TRY IF \<acute>run_hi = \<acute>hi THEN \<acute>ret_value:==1;;\<acute>ret :== \<acute>array;; THROW FI;;
                IF \<acute>array ! \<acute>run_hi < \<acute>array ! \<acute>lo
                THEN \<acute>run_hi :== \<acute>run_hi + 1;;
                  WHILE \<acute>run_hi < \<acute>hi \<and>
                        \<acute>array ! \<acute>run_hi < \<acute>array ! (\<acute>run_hi - 1)
                  INV \<lbrace> \<acute>lo<\<acute>run_hi \<and> \<acute>run_hi\<le>\<acute>hi \<and>
                    size \<acute>array = size \<^bsup>\<sigma>\<^esup>array \<and>
                    \<^bsup>\<sigma>\<^esup>array\<noteq>[] \<and> \<acute>hi \<le> size \<^bsup>\<sigma>\<^esup>array \<and>
                    \<acute>lo = \<^bsup>\<sigma>\<^esup>lo \<and> \<acute>hi = \<^bsup>\<sigma>\<^esup>hi\<rbrace> 
                  DO \<acute>run_hi :== \<acute>run_hi + 1 OD;;
                  \<acute>array :== CALL reverse_range(\<acute>array, \<acute>lo, \<acute>run_hi)
                ELSE \<acute>run_hi :== \<acute>run_hi + 1;;
                  WHILE \<acute>run_hi < \<acute>hi \<and>
                        \<acute>array ! (\<acute>run_hi - 1) \<le> \<acute>array ! \<acute>run_hi 
                  INV \<lbrace> \<acute>lo<\<acute>run_hi \<and> \<acute>run_hi\<le>\<acute>hi \<and>
                    size \<acute>array = size \<^bsup>\<sigma>\<^esup>array \<and>
                    \<acute>lo = \<^bsup>\<sigma>\<^esup>lo \<and> \<acute>hi = \<^bsup>\<sigma>\<^esup>hi\<rbrace> 
                  DO \<acute>run_hi :== \<acute>run_hi + 1 OD
                FI;;
                \<acute>ret_value :== \<acute>run_hi - \<acute>lo;;
                \<acute>ret :== \<acute>array
            CATCH SKIP END" in HoarePartial.annotateI)
  apply vcg
  apply auto
  done



lemma sumn_equal:"\<forall>i. i\<ge>0 \<and> i<n\<longrightarrow> xs!i=ys!i \<Longrightarrow> sumn xs n = sumn ys n"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have sn:"sumn xs n = sumn ys n" by simp
  from Suc.prems have an:"xs!n = ys!n" by blast
  from sn an show ?case by simp
qed



lemma (in sort_impl) sort_spec:
"\<forall>\<sigma>. \<Gamma>\<turnstile> \<lbrace>\<sigma>. (\<acute>array \<noteq> []) \<and> (\<acute>lo \<ge> 0) \<and>
(\<acute>lo +2\<le> \<acute>hi) \<and> (\<acute>hi \<le> size \<acute>array) \<and> (\<acute>hi - \<acute>lo \<ge> 16) \<and> (length \<acute>array < 2917196496) \<rbrace> (* if lo + 1 = hi then the array is already sorted *)
PROC sort(\<acute>array, \<acute>lo, \<acute>hi, \<acute>ret) 
\<lbrace> True\<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (hoare_rule anno = "
             TRY \<acute>n_remaining :== \<acute>hi - \<acute>lo;; IF \<acute>n_remaining < 2 THEN \<acute>ret :== \<acute>array;; THROW FI;;
                IF \<acute>n_remaining < 32
                THEN 
                  CALL count_run_and_make_ascending(\<acute>array, \<acute>lo, \<acute>hi, \<acute>init_run_len_i, \<acute>array);;
                  \<acute>array :== CALL binary_sort(\<acute>array, \<acute>lo, \<acute>hi, \<acute>lo+\<acute>init_run_len_i);; 
                  \<acute>ret :== \<acute>array;; THROW
                FI;;
            \<acute>a :== \<acute>array;; \<acute>stack_size :== 0;; \<acute>min_run :== 16;;
            IF size \<acute>a < 120 THEN \<acute>stack_len :== 4 ELSE
            IF size \<acute>a < 1542 THEN \<acute>stack_len :== 9 ELSE
            IF size \<acute>a < 119151 THEN \<acute>stack_len :== 18 ELSE
            \<acute>stack_len :== 39 FI FI FI;;
            \<acute>run_len :== replicate \<acute>stack_len (0::nat);;
            \<acute>run_base :== replicate \<acute>stack_len (0::nat);;
          CALL count_run_and_make_ascending(\<acute>a, \<acute>lo, \<acute>hi, \<acute>run_len_i, \<acute>a);;
          IF \<acute>run_len_i < \<acute>min_run
          THEN IF \<acute>n_remaining \<le> \<acute>min_run THEN \<acute>force :== \<acute>n_remaining ELSE \<acute>force :== \<acute>min_run FI;;
             \<acute>a :== CALL binary_sort(\<acute>a, \<acute>lo, \<acute>lo+\<acute>force, \<acute>lo+\<acute>run_len_i);;
             \<acute>run_len_i :== \<acute>force
          FI;;
          CALL push_run(\<acute>lo,\<acute>run_len_i);; CALL merge_collapse();; \<acute>lo :== \<acute>lo + \<acute>run_len_i;; \<acute>n_remaining :== \<acute>n_remaining - \<acute>run_len_i;;
            WHILE \<acute>n_remaining \<noteq> 0 
            INV \<lbrace> (\<acute>stack_size>0 \<and> \<acute>stack_size \<le> size \<acute>run_len) \<and>
              (\<acute>n_remaining \<ge> 0) \<and> (\<acute>min_run \<ge> 16) \<and> (\<acute>lo + \<acute>n_remaining = \<acute>hi) \<and>
              (\<acute>lo =  \<^bsup>\<sigma>\<^esup>lo + sumn \<acute>run_len \<acute>stack_size) \<and>
              (\<forall>i. ((i\<ge>3 \<and> i\<le>\<acute>stack_size)\<longrightarrow>(elem_inv \<acute>run_len (\<acute>stack_size-i) 16))) \<and>
              (\<acute>stack_size\<ge>2 \<longrightarrow> elem_bigger_than_next \<acute>run_len (\<acute>stack_size-2)) \<and>
              (\<acute>stack_size\<ge>2 \<longrightarrow> elem_larger_than_bound \<acute>run_len (\<acute>stack_size-2) 16) \<and>
              (\<acute>stack_size\<ge>1 \<longrightarrow> elem_larger_than_bound \<acute>run_len (\<acute>stack_size-1) 1) \<and>
              (\<acute>n_remaining>0 \<longrightarrow> (\<acute>stack_size\<ge>1 \<longrightarrow> elem_larger_than_bound \<acute>run_len (\<acute>stack_size-1) 16)) \<and>
              (\<forall>i. ((i\<ge>0 \<and> i<\<acute>stack_size-1)\<longrightarrow>(\<acute>run_base!i + \<acute>run_len!i = \<acute>run_base!(i+1)))) \<and>
              (\<acute>stack_size > 0 \<longrightarrow> \<acute>run_base!0 = \<^bsup>\<sigma>\<^esup>lo) \<and>
              (\<acute>stack_size = 0 \<longrightarrow> (\<acute>n_remaining > 0 \<and> \<acute>run_base!0 = 0)) \<and>
              (* add from class invariant *)
              length \<acute>run_base = length \<acute>run_len \<and>
              (length \<acute>a < 120 \<longrightarrow> length \<acute>run_len = 4) \<and>
              (120 \<le> length \<acute>a \<and> length \<acute>a < 1542 \<longrightarrow> length \<acute>run_len = 9) \<and>
              (1542 \<le> length \<acute>a \<and> length \<acute>a < 119151 \<longrightarrow> length \<acute>run_len = 18) \<and>
              (119151 \<le> length \<acute>a \<and> length \<acute>a < 2917196496 \<longrightarrow> length \<acute>run_len = 39) \<and>
              (length \<acute>a < 2917196496) \<and>
              (\<acute>run_base ! 0 + sumn \<acute>run_len \<acute>stack_size \<le> length \<acute>a) \<and>
              (\<acute>stack_size \<le> length \<acute>run_base) \<and>
              (\<acute>hi =  \<^bsup>\<sigma>\<^esup>hi) \<and> (\<^bsup>\<sigma>\<^esup>hi \<le> length \<acute>a)\<rbrace>
            DO CALL count_run_and_make_ascending(\<acute>a, \<acute>lo, \<acute>hi ,\<acute>run_len_i, \<acute>a);;
               IF \<acute>run_len_i < \<acute>min_run
               THEN IF \<acute>n_remaining \<le> \<acute>min_run
                    THEN \<acute>force :== \<acute>n_remaining
                    ELSE \<acute>force :== \<acute>min_run FI;;
                 \<acute>a :== CALL binary_sort(\<acute>a, \<acute>lo, \<acute>lo+\<acute>force, \<acute>lo+\<acute>run_len_i);;
                 \<acute>run_len_i :== \<acute>force
               FI;;
               CALL push_run(\<acute>lo,\<acute>run_len_i);;
               CALL merge_collapse();; \<acute>lo :== \<acute>lo + \<acute>run_len_i;;
               \<acute>n_remaining :== \<acute>n_remaining - \<acute>run_len_i 
            OD;;
            CALL merge_force_collapse();;
            \<acute>ret :== \<acute>a
            CATCH Skip END" in HoarePartial.annotateI)
  apply vcg
    apply (simp_all only:invariant_def)
    apply clarsimp
    apply (rule conjI)
  using add.commute apply auto[1]
    apply (simp add:elem_larger_than_bound_def)
    apply (intro conjI impI)
       apply (intro allI)
       apply clarsimp
     apply (intro conjI impI)
            apply fastforce
           apply fastforce
          apply fastforce
         apply fastforce
        apply (clarsimp)
        apply (rule conjI)
         apply (clarsimp)+
       apply fastforce
      apply fastforce
     apply clarsimp
     apply (rule conjI)
      apply (clarsimp)+
    apply (intro conjI impI)
          apply fastforce
         apply fastforce
        apply fastforce
       apply clarsimp
       apply (rule conjI)
        apply clarsimp
       apply clarsimp
      apply fastforce
     apply fastforce
    apply clarsimp
    apply (rule conjI)
     apply clarsimp
    apply clarsimp

(* finish p \<longrightarrow> inv *)
   apply clarify
   apply simp
   apply (intro conjI impI)
       apply clarsimp
      apply (simp add:elem_inv_def)+
    apply (simp add:elem_larger_than_bound_def)
   apply (intro allI)
   apply clarsimp
   apply (intro conjI impI)
          apply clarsimp
  using run_len_iter apply (metis One_nat_def add.commute) 
        apply clarsimp
        apply (intro conjI impI)
          apply (simp add:elem_inv_def elem_larger_than_bound_def elem_bigger_than_next_2_def)
          apply (simp add:elem_bigger_than_next_def)
         apply force
  using sumn_equal apply presburger
       apply clarsimp
  using run_len_iter apply (metis One_nat_def add.commute)
     apply clarsimp
     apply (intro conjI impI)
       apply (simp add:elem_inv_def elem_larger_than_bound_def elem_bigger_than_next_2_def)
       apply (simp add:elem_bigger_than_next_def)
      apply force
  using sumn_equal apply presburger
  using run_len_iter  apply (metis One_nat_def add.commute) 
  apply clarsimp
   apply (intro conjI impI)
     apply (simp add:elem_inv_def elem_larger_than_bound_def elem_bigger_than_next_2_def)
     apply (simp add:elem_bigger_than_next_def)
    apply force
  using sumn_equal apply presburger
   apply (simp only:elem_larger_than_bound_def)
(* finish {inv} c {inv} *)
  apply (intro conjI impI)
                   apply (simp_all add:elem_larger_than_bound_def elem_inv_def elem_bigger_than_next_2_def elem_bigger_than_next_def)
  apply (subgoal_tac "length a \<noteq> 0")
   apply clarsimp
  apply clarsimp
  apply (case_tac "stack_size")
   apply clarify
  using sumn.simps apply clarsimp
  done 


end