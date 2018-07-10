theory TimSortLemma
  imports  Main "~~/src/HOL/Library/Code_Target_Numeral" 
begin
definition list_copy :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
"list_copy xs n ys m l = (take n xs) @ (take l (drop m ys)) @ (drop (n+l) xs)"

value "[1,2,3,4,5::int]"

value "let a = [1::nat,2,3,4,5] in list_copy a 1 a 0 5"
(* make sure (n+l\<le>length xs & (m+l)\<le>length ys*)

lemma list_copy_front:"n<length xs \<and> m<length ys \<and> (m+l)\<le>length ys \<Longrightarrow> take n (list_copy xs n ys m l) = take n xs"
  by (simp add:list_copy_def)

lemma list_copy_middle:"n<length xs & m<length ys& (m+l)\<le>length ys \<Longrightarrow> 
          take l (drop n (list_copy xs n ys m l)) = take l (drop m ys)"
  by (auto simp add:list_copy_def)

lemma list_copy_end:"n<length xs & m<length ys& (m+l)\<le>length ys \<Longrightarrow> drop (n+l) (list_copy xs n ys m l) = drop (n+l) xs"
  apply (auto simp add:list_copy_def)
  apply (metis diff_add_inverse2 le_add_diff_inverse less_imp_le_nat min.absorb2 nat_add_left_cancel_le)
  done

lemma list_copy_len[simp]:"(m+l)\<le>length ys \<Longrightarrow> (n+l)\<le>length xs \<Longrightarrow> (length (list_copy xs n ys m l) = length xs)"
  by (auto simp add:list_copy_def)

lemma list_copy_zero:"list_copy xs n ys m 0 = xs"
  by (simp add:list_copy_def)

definition sorted_in::"int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"sorted_in xs lo hi = (\<forall>i. (i\<ge>lo\<and>i<hi)\<longrightarrow>(xs!i\<le>xs!(i+1)))"

thm allE
value "sorted [0,-1::int]"
value "([0::int,-1]!0) \<le>([0::int,-1]!1)"
lemma sorted_in_one_more: "sorted_in xs lo hi \<Longrightarrow> sorted_in (x#xs) (Suc lo) (Suc hi)"
  apply (auto simp add:sorted_in_def)
  apply (erule_tac ?x = "i-1" in allE)
  apply auto
  done

lemma sorted_in_conca:"sorted_in xs lo mid \<and> sorted_in xs mid hi \<Longrightarrow> sorted_in xs lo hi"
  apply (auto simp add:sorted_in_def)
  using not_less by blast

lemma sorted_in_hi:"sorted_in xs lo hi \<and> xs!hi<xs!(hi+1) \<Longrightarrow> sorted_in xs lo (hi+1)"
  apply (auto simp add:sorted_in_def)
  using less_antisym by fastforce

lemma sorted_in_pick_two:"sorted_in xs lo hi \<and> i\<ge>lo \<and> j\<le>hi \<and> i\<le>j \<Longrightarrow> xs!i \<le> xs!j"
  apply (simp add:sorted_in_def)
  apply (induct j arbitrary:xs lo hi i)
   apply simp
  apply (case_tac "i=Suc j")
   apply simp
  apply (subgoal_tac "xs ! i \<le> xs ! j")
  apply (meson Suc_le_lessD dual_order.trans le_SucE)
  by (meson Suc_leD le_SucE)

lemma le_half:"a<(b::nat) \<Longrightarrow> (a+b) div 2 < b"
proof -
  assume le:"a<b"
  from this have "a+b<b+b" by simp
  from this have "(a+b) div 2 < (b+b) div 2"
    using div_le_mono by auto
  from this show ?thesis
    by linarith
qed

lemma conca_nth_a[simp]:" i < length xs \<Longrightarrow> (xs@ys)!i = xs!i"
  using nth_take[of i "length xs" "xs@ys"] by auto
lemma conca_nth_b[simp]:" i\<ge> length xs \<Longrightarrow> (xs@ys)!i = ys!(i-length xs)"
  by (simp add: nth_append)
lemma list_copy_i_front[simp]:"(n+l)\<le>length xs \<Longrightarrow> (m+l)\<le>length ys \<Longrightarrow> i<n \<Longrightarrow> (list_copy xs n ys m l)!i = xs!i"
  apply (auto simp add:list_copy_def)
  done
lemma list_copy_i_mid[simp]:"(n+l)\<le>length xs \<Longrightarrow> (m+l)\<le>length ys \<Longrightarrow> i\<ge>n\<and>i<(n+l) \<Longrightarrow> (list_copy xs n ys m l)!i = ys!(i-n+m)"
  apply (auto simp add:list_copy_def)
  apply (subgoal_tac "min (length xs) n = n")
   apply (simp)
   apply (subgoal_tac "i-n < l")
    apply (auto simp add:add.commute)
  done
  
lemma list_copy_i_end[simp]:"(n+l)\<le>length xs \<Longrightarrow> (m+l)\<le>length ys \<Longrightarrow> i\<ge>n+l\<and>i<length xs \<Longrightarrow> (list_copy xs n ys m l)!i = xs!i"
  apply (auto simp add:list_copy_def)
  apply (subgoal_tac "min (length xs) n + min (length ys - m) l = n+l")
   apply auto
  done
lemma length_take_one:"n\<le>length xs \<Longrightarrow>length (take n xs) =  n"
  by auto

definition elem_bigger_than_next_2::"nat list \<Rightarrow> nat \<Rightarrow> bool"
  where "elem_bigger_than_next_2 array index \<equiv>
      (index+2<(size array)) \<longrightarrow>
      (array!index) > (array!(index+1)) + (array!(index+2))"

definition elem_bigger_than_next::"nat list \<Rightarrow> nat \<Rightarrow> bool"
  where "elem_bigger_than_next array index \<equiv>
      (index+1<(size array)) \<longrightarrow>
      (array!index) > (array!(index+1))"

definition elem_larger_than_bound::"nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where "elem_larger_than_bound array index bound \<equiv>
      (index<(size array)) \<longrightarrow> (array!index) \<ge> bound"

definition elem_inv::"nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where "elem_inv array index bound \<equiv>
      (elem_bigger_than_next_2 array index) \<and>
      (elem_bigger_than_next array index) \<and>
      (elem_larger_than_bound array index bound)"


value "(1::int)#2#3#[]"
value "last ((1::int)#2#3#[])"
value "butlast ((1::int)#2#3#[])"

value "((1::int)#2#3#[])!2"
value "take 2 ((1::int)#2#3#[])"
value "((1::int)#2#3#[])[2:=10]"
value "replicate 5 (6::nat)"
value "if (3::nat)>4 then 5::nat else (if (3::nat)>4 then 7 else 8)"

value "if 150 < (120::nat) then (4::nat) else 
                (if (150::nat) < 1542 then (9::nat) else
                 (if (150::nat) < 119151 then (18::nat) else (39::nat)))"

lemma suc_simp:"Suc n = n+1"
  by simp

primrec sum :: "nat list \<Rightarrow> nat"
  where
"sum [] = 0" |
"sum (x#xs) = x+(sum xs)"

primrec sumn :: "nat list \<Rightarrow> nat \<Rightarrow> nat"
  where
"sumn a 0 = 0" |
"sumn a (Suc n) = a!n + (sumn a n)"

value "sumn (1#2#3#[]) 2"

fun fib:: "nat \<Rightarrow> nat" where
"fib 0 = 1" |
"fib (Suc 0) = 1" |
"fib (Suc (Suc n)) = fib(n) + fib(Suc n)"


fun fib2:: "nat \<Rightarrow> nat" where
"fib2 0 = 0" |
"fib2 (Suc 0) = 1" |
"fib2 (Suc (Suc n)) = fib2(n) + fib2(Suc n) + 1"

lemma fib_plus_2: "fib(n+2) = fib(n+1) + fib(n)"
  by auto

lemma fib2_plus_2: "fib2(n+2) = fib2(n+1) + fib2(n) + 1"
  by auto

value "((fib 5) - 1)*16 + (fib2 5) - (5)"
value "((fib 19) - 1)*16 + (fib2 19) - (19)"

value "fib 3"
value "fib2 3"
term "15::nat"





(* lemma for push_run_spec *)
lemma less_than: "\<lbrakk>(a::nat)\<le>(b::nat); a\<noteq>b\<rbrakk> \<Longrightarrow> a<b"
  by simp

lemma sum_append_one: "sum(a@[(b::nat)]) = sum a + b"
  apply (induction a)
   apply auto
  done

lemma accu_add: "\<lbrakk>\<forall>i<(n-1). a!i + b!i = a!(i+1);size a = size b; size a \<ge> n; size a > 0; n > 0\<rbrakk> \<Longrightarrow> 
  a!(n-1)+b!(n-1) = a!(0) + (sum (take n b))"
  apply (induction n)
   apply auto
  apply (case_tac "n=0")
   apply (auto simp add: take_Suc_conv_app_nth)
  using sum_append_one by auto

lemma list_take_and_drop: "xs = take n xs @ drop n xs"
  by auto

lemma sumn_update_no_use: "m\<le>length a \<Longrightarrow> n\<ge>m \<Longrightarrow>sumn (a[n:=t]) m = sumn a m"
  apply (induct m arbitrary: a t n)
   apply (auto)
  done

lemma sumn1:"n\<ge>2 \<Longrightarrow> n\<le>length a \<Longrightarrow> sumn (a[n - 2 := a ! (n - 2) + a ! Suc (n - 2)]) (n - Suc 0) = sumn a n"
  apply (case_tac n)
   apply simp_all
  apply (case_tac nat)
   apply (simp_all add:sumn_update_no_use)
  done


lemma sumn2: "n\<ge>3 \<Longrightarrow> n \<le> length a \<Longrightarrow> sumn (a[n - 3 := a ! (n - 3) + a ! Suc (n - 3),
                     Suc (n - 3) := a ! Suc (Suc (n - 3))]) (n - Suc 0) = sumn a n"
  apply (case_tac n)
   apply simp_all
  apply (case_tac nat)
   apply (simp_all)
  apply (case_tac nata)
   apply (simp_all)
  apply (simp_all add:sumn_update_no_use)
  done

lemma nth_list_update_neq2: "i \<noteq> j \<Longrightarrow> k \<noteq> j \<Longrightarrow> xs[i:=x,k:=y]!j = xs!j"
  apply (induct xs arbitrary:i j k)
   apply (auto simp add: nth_Cons split: nat.split)
  done
(* lemma for merge_at_spec *)

lemma run_len_iter: "\<forall>i<l - Suc 0. ys ! i + xs ! i = ys ! Suc i \<Longrightarrow>
                     l > 0 \<Longrightarrow>
                     l \<le> size xs \<Longrightarrow>
                     size xs = size ys \<Longrightarrow>
                    ys!0 + sumn xs l = xs!(l-1) + ys!(l-1)"
proof (induction l arbitrary: xs ys)
  case 0
  then show ?case by simp
next
  case (Suc l)
  from Suc.IH Suc.prems show ?case
  proof (cases "l=0")
    case True
    then show ?thesis by simp
  next
    case False
    assume a0:"length xs = length ys" and a1:"Suc l \<le> length xs" and a2:"0 < Suc l" and a3:"l \<noteq> 0" and a4:" \<forall>i<Suc l - Suc 0. ys ! i + xs ! i = ys ! Suc i" and
          a5: "(\<And>ys xs. \<forall>i<l - Suc 0. ys ! i + xs ! i = ys ! Suc i \<Longrightarrow> 0 < l \<Longrightarrow> l \<le> length xs \<Longrightarrow> length xs = length ys \<Longrightarrow> ys ! 0 + sumn xs l = xs ! (l - 1) + ys ! (l - 1))"
    from this have step0:"ys ! 0 + sumn xs l = xs ! (l - 1) + ys ! (l - 1)"
      by (metis Suc_diff_Suc Suc_diff_diff Suc_leD Suc_pred less_SucI not_gr_zero)
    from a2 a3 a4 have one_run:"ys!(l-1) + xs!(l-1) = ys!l"
      by (metis One_nat_def Suc_pred' diff_Suc_1 diff_Suc_less less_antisym) 
    from sumn.simps(2) have one_sumn:"sumn xs (l+1) = sumn xs l + xs!l" by simp
    from step0 one_run one_sumn show ?thesis by simp
  qed
qed

lemma rl_elem_lower_bound: "\<forall>i. 3\<le>i \<and> i\<le>l \<longrightarrow> (l-i < l-2 \<longrightarrow> rl!Suc (l-i) + rl!Suc (Suc (l-i)) < rl!(l-i)) \<and> (l-i < l-1 \<longrightarrow> rl!Suc (l-i) < rl!(l-i)) \<and> u \<le> rl!(l-i) \<Longrightarrow>
                             rl!(l-1) < rl!(l-2) \<Longrightarrow> u \<le> rl!(l-1) \<Longrightarrow> length rl = l \<Longrightarrow> l\<ge>2 \<Longrightarrow> k<l 
                             \<Longrightarrow> rl!(l-1-k) \<ge> u*(fib k) + (fib2 k)"
proof (induction k arbitrary:u rl l rule:fib2.induct)
  case 1
  then show ?case by auto
next
  case 2
  then have "rl!(l-2)\<ge>u+1" by simp
  then show ?case
    by (metis One_nat_def diff_diff_left fib.simps(2) fib2.simps(2) nat_mult_1_right one_add_one) 
next
  case (3 n)
  from this have n1:"u * fib n + fib2 n \<le> rl ! (l - 1 - n)" and n2:"u * fib (Suc n) + fib2 (Suc n) \<le> rl ! (l - 1 - Suc n)"
    by (metis Suc_lessD)+
  from "3.prems"  have larger_than_next_two:"rl ! (l - 1 - n) + rl ! (l - 1 - Suc n) < rl ! (l - 1 - Suc (Suc n))" 
    apply(drule_tac x="n+3" in spec)
    apply (clarsimp)
    apply (subgoal_tac "l - (n + 3) < l - 2")
     prefer 2
     apply linarith
    by (smt Suc_diff_Suc Suc_lessD add.commute add_2_eq_Suc' add_Suc_right nat_le_linear not_less numeral_2_eq_2 numeral_3_eq_3)
  from n1 n2 larger_than_next_two show ?case by (simp add:distrib_left)
qed

lemma append_suc: "n\<ge>1 \<Longrightarrow> length xs \<ge> n \<Longrightarrow> (x#xs)!n = xs!(n-1)"
proof (induction n arbitrary:xs x)
case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by force
qed 

lemma minus_same_num: "a=b \<Longrightarrow> a-c = b-c" by simp

lemma minus_suc_plus_one: "a + 1 - (Suc b) = a - b" by simp

lemma minus_exc: "a\<ge>c \<Longrightarrow> (a::nat)+b-c = a-c+b" by simp

lemma fib2_1: "fib2 n \<ge> n" 
  apply (induction n rule:fib2.induct)
    apply auto
  done

lemma fib_1:"fib n \<ge> Suc 0"
  apply (induction n rule:fib.induct)
    apply auto
  done

lemma sumn_first_one_out:"l \<le> length (a#rl) \<Longrightarrow> l > 0 \<Longrightarrow> sumn (a # rl) l = a + sumn rl (l - Suc 0)"
proof (induction l arbitrary: a rl)
  case 0
  then show ?case by simp
next
  case (Suc l)
  then show ?case
  proof (cases "l=0")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis using Suc.IH[of a rl] Suc.prems
      by (smt Suc_leD Suc_pred ab_semigroup_add_class.add_ac(1) add.commute diff_Suc_1 less_Suc_eq nth_Cons_pos sumn.simps(2)) 
    qed
qed

lemma rl_sum_lower_bound: "\<forall>i. 3\<le>i \<and> i\<le>l \<longrightarrow> (l-i < l-2 \<longrightarrow> rl!Suc (l-i) + rl!Suc (Suc (l-i)) < rl!(l-i)) \<and> (l-i < l-1 \<longrightarrow> rl!Suc (l-i) < rl!(l-i)) \<and> u \<le> rl!(l-i) \<Longrightarrow>
                             rl!(l-1) < rl!(l-2) \<Longrightarrow> u \<le> rl!(l-1) \<Longrightarrow> length rl = l \<Longrightarrow> l\<ge>2
                             \<Longrightarrow> sumn rl l \<ge> u*((fib (l+1))-1) + ((fib2 (l+1)) - (l+1))"
proof (induction rl arbitrary:u l)
  case Nil
  then show ?case by simp
next
  case (Cons a rl)
  then show ?case
  proof (cases "l=2")
    case True
    then show ?thesis using Cons.prems Cons.IH
      by (simp add: numeral_2_eq_2 numeral_3_eq_3)
  next
    case False
    from this have l3:"l\<ge>3" using Cons.prems by simp
    from this have a0:" l -1 \<ge> 2" by simp
    from Cons.prems have a1: "\<forall>i. 3 \<le> i \<and> i \<le> l - 1 \<longrightarrow>
        (l - 1 - i < l - 1 - 2 \<longrightarrow> rl ! Suc (l - 1 - i) + rl ! Suc (Suc (l - 1 - i)) < rl ! (l - 1 - i)) \<and>
        (l - 1 - i < l - 1 - 1 \<longrightarrow> rl ! Suc (l - 1 - i) < rl ! (l - 1 - i)) \<and> u \<le> rl ! (l - 1 - i) \<Longrightarrow>
    rl ! (l - 1 - 1) < rl ! (l - 1 - 2)"
      apply (clarsimp)
      by (metis False One_nat_def diff_Suc_eq_diff_pred less_than nth_Cons_pos numeral_2_eq_2 zero_less_diff)
    from Cons.prems a0 have a2:"rl ! (l - 1 - 1) < rl ! (l - 1 - 2)" 
      using l3 by (simp add: numeral_2_eq_2)
    from Cons.prems have a3:"u \<le> rl ! (l - 1 - 1)"
      by (simp)
    from Cons.prems have a4:"length rl = l - 1"
      by (simp)
    from Cons.IH[of "l-1" u] a0 a1 a2 a3 a4 have l1:"u * (fib (l - 1 + 1) - 1) + (fib2 (l - 1 + 1) - (l - 1 + 1)) \<le> sumn rl (l - 1)"
      apply clarsimp
      using Cons.prems by (smt Suc_diff_le Suc_le_lessD Suc_less_eq Suc_pred diff_Suc_1 diff_Suc_Suc nat_less_le nth_Cons_pos numeral_2_eq_2 zero_less_Suc)
    from Cons.prems have la:"a \<ge> u*(fib (l-1)) + (fib2 (l-1))" using rl_elem_lower_bound[of l "a#rl" u "l-1"]
      by (metis One_nat_def a4 diff_self_eq_0 less_add_same_cancel1 less_numeral_extra(1) list.size(4) nth_Cons_0)
    have "fib2 l + fib2 (l - Suc 0) + 1 = fib2 (Suc l) "  using fib2.simps(3)[of "l - Suc 0"] Cons.prems(5) by simp
    from this have "fib2 l + fib2 (l - Suc 0) + 1 - Suc l = fib2 (Suc l) - Suc l" using minus_same_num by simp
    from this have "fib2 l + fib2 (l - Suc 0) - l = fib2 (Suc l) - Suc l" using minus_suc_plus_one by simp
    from this have f2:"fib2 l - l + fib2 (l - Suc 0) = fib2 (Suc l) - Suc l" using minus_exc fib2_1  by metis
    have "fib l +  fib (l - Suc 0) = fib (Suc l)" using fib.simps(3) Cons.prems(5) by (metis Cons.prems(4) One_nat_def a4 add.commute length_Cons) 
    from this have "(fib l - Suc 0) + fib (l - Suc 0) = (fib (Suc l) - Suc 0)" using Cons.prems(5) minus_exc fib_1 by metis
    from this have f1:"u * (fib l - Suc 0) + u * fib (l - Suc 0) = u * (fib (Suc l) - Suc 0)" by (metis add_mult_distrib2)
    from l1 la show ?thesis 
      apply (subgoal_tac "sumn (a # rl) l = a + sumn rl (l-1)")
       apply clarsimp
       apply (subgoal_tac "u * (fib (Suc (l - Suc 0)) - Suc 0) + u * fib (l - Suc 0) = u * (fib (Suc l) - Suc 0)" 
                          "(fib2 (Suc (l - Suc 0)) - Suc (l - Suc 0)) + fib2 (l - Suc 0) = (fib2 (Suc l) - Suc l)")
         apply simp
      using Cons.prems(5) f1 f2 apply simp_all
      using Cons.prems sumn_first_one_out by simp
  qed
qed

value "16 * (fib 5 - Suc 0) + (fib2 5 - 5)" (* = 199 *)
axiomatization where l119[simp]: "16 * (fib 5 - Suc 0) + (fib2 5 - 5) = 119"
value "16 * (fib 10 - Suc 0) + (fib2 10 - 10)" (* = 1541 *)
axiomatization where l1541[simp]: "16 * (fib 10 - Suc 0) + (fib2 10 - 10) = 1541"
value "16 * (fib 19 - Suc 0) + (fib2 19 - 19)" (* = 119150 *)
axiomatization where l119150[simp]: "16 * (fib 19 - Suc 0) + (fib2 19 - 19) = 119150"
value "16 * (fib 40 - Suc 0) + (fib2 40 - 40)" (* = 2917196495 *)
axiomatization where l2917[simp]: "16 * (fib 40 - Suc 0) + (fib2 40 - 40) = 2917196495"


lemma run_len_elem_lower_bound: "
\<forall>i. 3\<le>i \<and> i\<le>l \<longrightarrow> elem_inv rl (l-i) u \<Longrightarrow>
elem_bigger_than_next rl (l-2) \<Longrightarrow>
elem_larger_than_bound rl (l-1) u \<Longrightarrow> length rl = l \<Longrightarrow> l\<ge>2 \<Longrightarrow> k<l 
\<Longrightarrow> rl!(l-1-k) \<ge> u*(fib k) + (fib2 k)"
  apply (simp only:elem_inv_def elem_larger_than_bound_def elem_bigger_than_next_2_def elem_bigger_than_next_def)
  apply (rule rl_elem_lower_bound)
       apply auto
  by (metis Suc_diff_le diff_Suc_Suc numeral_2_eq_2)

lemma run_len_sum_lower_bound: "
\<forall>i. 3\<le>i \<and> i\<le>l \<longrightarrow> elem_inv rl (l-i) u \<Longrightarrow>
elem_bigger_than_next rl (l-2) \<Longrightarrow> 
elem_larger_than_bound rl (l-1) u \<Longrightarrow> length rl = l \<Longrightarrow> l\<ge>2
\<Longrightarrow> sumn rl l \<ge> u*((fib (l+1))-1) + ((fib2 (l+1)) - (l+1))"
  apply (rule rl_sum_lower_bound)
      apply (auto simp add:elem_inv_def elem_larger_than_bound_def elem_bigger_than_next_2_def elem_bigger_than_next_def)
  by (metis Suc_diff_le diff_Suc_Suc numeral_2_eq_2)

(*
lemma "
elem_inv rl 0 u \<Longrightarrow>
 elem_inv rl 1 u \<Longrightarrow> 
elem_bigger_than_next rl 2 \<Longrightarrow> 
elem_larger_than_bound rl 3 u \<Longrightarrow>
length rl = 4 \<Longrightarrow> u \<ge> 16 
\<Longrightarrow> sum rl \<ge> 119"
  apply (simp add:elem_inv_def elem_larger_than_bound_def elem_bigger_than_next_2_def elem_bigger_than_next_def)
  apply (case_tac rl)
   prefer 2
   apply (case_tac list)
    prefer 2
    apply (case_tac lista)
     prefer 2
     apply (case_tac listb)
      apply auto
  done
*)

end