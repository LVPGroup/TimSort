theory GallopA
  imports "TimSortProc"
begin



lemma (in gallop_left_impl) gallop_left_modifies:
  shows
  "\<forall> \<sigma>. \<Gamma>\<turnstile> {\<sigma>} \<acute>ret:== PROC gallop_left(\<acute>key, \<acute>array, \<acute>base, \<acute>len, \<acute>hint)
            {t. t may_only_modify_globals \<sigma> in []}"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply (vcg spec=modifies)
  done

lemma (in gallop_right_impl) gallop_right_modifies:
  shows
  "\<forall> \<sigma>. \<Gamma>\<turnstile> {\<sigma>} \<acute>ret:== PROC gallop_right(\<acute>key, \<acute>array, \<acute>base, \<acute>len, \<acute>hint)
            {t. t may_only_modify_globals \<sigma> in []}"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (vcg spec=modifies)
  done

lemma (in merge_lo_impl) merge_lo_modifies:
  shows
  "\<forall> \<sigma>. \<Gamma>\<turnstile> {\<sigma>} PROC merge_lo(\<acute>base1, \<acute>len1, \<acute>base2, \<acute>len2)
            {t. t may_only_modify_globals \<sigma> in [a]}"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (vcg spec=modifies)
  done

lemma (in merge_hi_impl) merge_hi_modifies:
  shows
  "\<forall> \<sigma>. \<Gamma>\<turnstile> {\<sigma>} PROC merge_hi(\<acute>base1, \<acute>len1, \<acute>base2, \<acute>len2)
            {t. t may_only_modify_globals \<sigma> in [a]}"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (vcg spec=modifies)
  done

lemma (in gallop_left_impl) gallop_left_spec:
  shows
  "\<forall>\<sigma>. \<Gamma>\<turnstile> \<lbrace> \<sigma>. \<acute>array\<noteq>[] \<and> \<acute>base\<ge>0 \<and> \<acute>len>0 \<and> \<acute>hint<\<acute>len \<and> \<acute>base+\<acute>len\<le>length \<acute>array\<rbrace>
  \<acute>ret :== PROC gallop_left(\<acute>key, \<acute>array, \<acute>base, \<acute>len, \<acute>hint)
  \<lbrace> \<acute>ret \<ge>0 \<and> \<acute>ret \<le>\<acute>len \<and> \<acute>len = \<^bsup>\<sigma>\<^esup>len\<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (hoare_rule anno="
          \<acute>last_ofs :== 0;; \<acute>ofs :== 1;;
            IF \<acute>array ! (\<acute>base + \<acute>hint) < \<acute>key
            THEN \<acute>max_ofs :== \<acute>len - \<acute>hint;;
              WHILE \<acute>ofs < \<acute>max_ofs \<and> \<acute>array ! (\<acute>base + \<acute>hint + \<acute>ofs) < \<acute>key 
              INV \<lbrace> \<acute>ofs>0 \<and> \<acute>last_ofs\<ge>0 \<and> \<acute>last_ofs<\<acute>ofs \<and> \<acute>last_ofs<\<acute>max_ofs \<and>
                    \<acute>base = \<^bsup>\<sigma>\<^esup>base \<and> \<acute>len = \<^bsup>\<sigma>\<^esup>len \<and> \<acute>hint = \<^bsup>\<sigma>\<^esup>hint \<and> \<acute>hint<\<acute>len \<and>
                    \<acute>max_ofs = \<acute>len-\<acute>hint \<rbrace>
              DO \<acute>last_ofs :== \<acute>ofs;; \<acute>ofs :== \<acute>ofs + \<acute>ofs + 1 OD;;
              IF \<acute>max_ofs < \<acute>ofs THEN \<acute>ofs :== \<acute>max_ofs FI;; \<acute>last_ofs :== \<acute>last_ofs + \<acute>hint + 1;; \<acute>ofs :== \<acute>ofs + \<acute>hint
            ELSE \<acute>max_ofs :== \<acute>hint + 1;;
              WHILE \<acute>ofs < \<acute>max_ofs \<and> \<acute>key \<le> \<acute>array ! (\<acute>base + \<acute>hint - \<acute>ofs) 
              INV \<lbrace> \<acute>ofs>0 \<and> \<acute>last_ofs\<ge>0 \<and> \<acute>last_ofs<\<acute>ofs \<and> \<acute>last_ofs<\<acute>max_ofs \<and>
                    \<acute>base = \<^bsup>\<sigma>\<^esup>base \<and>  \<acute>len = \<^bsup>\<sigma>\<^esup>len \<and> \<acute>hint = \<^bsup>\<sigma>\<^esup>hint \<and> \<acute>hint<\<acute>len \<rbrace>
              DO \<acute>last_ofs :== \<acute>ofs;; \<acute>ofs :== \<acute>ofs + \<acute>ofs + 1 OD;;
              IF \<acute>max_ofs < \<acute>ofs THEN \<acute>ofs :== \<acute>max_ofs FI;; \<acute>tmp_gallop :== \<acute>last_ofs;; \<acute>last_ofs :== \<acute>hint + 1 - \<acute>ofs;;
              \<acute>ofs :== \<acute>hint - \<acute>tmp_gallop
            FI;;
            WHILE \<acute>last_ofs < \<acute>ofs 
            INV \<lbrace> \<acute>last_ofs\<ge>0 \<and> \<acute>last_ofs\<le>\<acute>ofs \<and> \<acute>ofs\<le>\<acute>len \<and>
                  \<acute>last_ofs \<le> (\<acute>ofs+\<acute>last_ofs)div 2 \<and> \<acute>ofs \<ge> (\<acute>ofs+\<acute>last_ofs)div 2 \<and>
                  \<acute>len = \<^bsup>\<sigma>\<^esup>len \<and> \<acute>base = \<^bsup>\<sigma>\<^esup>base \<rbrace>
            DO \<acute>mid :== (\<acute>ofs + \<acute>last_ofs) div 2;; IF \<acute>array ! (\<acute>base + \<acute>mid) < \<acute>key THEN \<acute>last_ofs :== \<acute>mid + 1 ELSE \<acute>ofs :== \<acute>mid FI OD;;
            \<acute>ret :== \<acute>ofs
        " in HoarePartial.annotateI)
  apply vcg
  by auto 
  

lemma (in gallop_right_impl) gallop_right_spec:
  shows
  "\<forall>\<sigma>. \<Gamma>\<turnstile> \<lbrace> \<sigma>. \<acute>array\<noteq>[] \<and> \<acute>base\<ge>0 \<and> \<acute>len>0 \<and> \<acute>hint<\<acute>len \<and> \<acute>base+\<acute>len\<le>length \<acute>array\<rbrace>
  \<acute>ret :== PROC gallop_right(\<acute>key, \<acute>array, \<acute>base, \<acute>len, \<acute>hint)
  \<lbrace> \<acute>ret \<ge>0 \<and> \<acute>ret \<le>\<acute>len \<and> \<acute>len = \<^bsup>\<sigma>\<^esup>len\<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (hoare_rule anno="
         \<acute>last_ofs :== 0;; \<acute>ofs :== 1;;
            IF \<acute>key < \<acute>array ! (\<acute>base + \<acute>hint)
            THEN \<acute>max_ofs :== \<acute>hint + 1;;
              WHILE \<acute>ofs < \<acute>max_ofs \<and> \<acute>key < \<acute>array ! (\<acute>base + \<acute>hint - \<acute>ofs)
              INV \<lbrace> \<acute>ofs>0 \<and> \<acute>last_ofs\<ge>0 \<and> \<acute>last_ofs<\<acute>ofs \<and> \<acute>last_ofs<\<acute>max_ofs \<and>
                    \<acute>base = \<^bsup>\<sigma>\<^esup>base \<and>  \<acute>len = \<^bsup>\<sigma>\<^esup>len \<and> \<acute>hint = \<^bsup>\<sigma>\<^esup>hint \<and> \<acute>hint<\<acute>len
                    \<rbrace> 
              DO \<acute>last_ofs :== \<acute>ofs;; \<acute>ofs :== \<acute>ofs + \<acute>ofs + 1 OD;;
              IF \<acute>max_ofs < \<acute>ofs THEN \<acute>ofs :== \<acute>max_ofs FI;;
              \<acute>tmp_gallop :== \<acute>last_ofs;; \<acute>last_ofs :== \<acute>hint + 1 - \<acute>ofs;;
              \<acute>ofs :== \<acute>hint - \<acute>tmp_gallop
            ELSE \<acute>max_ofs :== \<acute>len - \<acute>hint;;
              WHILE \<acute>ofs < \<acute>max_ofs \<and> \<acute>array ! (\<acute>base + \<acute>hint + \<acute>ofs) \<le> \<acute>key
              INV \<lbrace> \<acute>ofs>0 \<and> \<acute>last_ofs\<ge>0 \<and> \<acute>last_ofs<\<acute>ofs \<and> \<acute>last_ofs<\<acute>max_ofs \<and>
                    \<acute>base = \<^bsup>\<sigma>\<^esup>base \<and> \<acute>len = \<^bsup>\<sigma>\<^esup>len \<and> \<acute>hint = \<^bsup>\<sigma>\<^esup>hint \<and> \<acute>hint<\<acute>len \<and>
                    \<acute>max_ofs = \<acute>len-\<acute>hint \<rbrace> 
              DO \<acute>last_ofs :== \<acute>ofs;; \<acute>ofs :== \<acute>ofs + \<acute>ofs + 1 OD;;
              IF \<acute>max_ofs < \<acute>ofs THEN \<acute>ofs :== \<acute>max_ofs FI;;
              \<acute>last_ofs :== \<acute>last_ofs + \<acute>hint + 1;; \<acute>ofs :== \<acute>ofs + \<acute>hint
            FI;;
            WHILE \<acute>last_ofs < \<acute>ofs 
            INV \<lbrace> \<acute>last_ofs\<ge>0 \<and> \<acute>last_ofs\<le>\<acute>ofs \<and> \<acute>ofs\<le>\<acute>len \<and>
                  \<acute>last_ofs \<le> (\<acute>ofs+\<acute>last_ofs)div 2 \<and> \<acute>ofs \<ge> (\<acute>ofs+\<acute>last_ofs)div 2 \<and>
                  \<acute>len = \<^bsup>\<sigma>\<^esup>len \<and> \<acute>base = \<^bsup>\<sigma>\<^esup>base \<rbrace>
            DO \<acute>mid :== (\<acute>ofs + \<acute>last_ofs) div 2;;
               IF \<acute>key < \<acute>array ! (\<acute>base + \<acute>mid) THEN \<acute>ofs :== \<acute>mid
               ELSE \<acute>last_ofs :== \<acute>mid+1 FI 
            OD;;
            \<acute>ret :== \<acute>ofs
      " in HoarePartial.annotateI)
   apply vcg
   by auto  



 lemma (in merge_lo_impl) merge_lo_spec:
  shows
  "\<forall>\<sigma>. \<Gamma>\<turnstile> \<lbrace> \<sigma>. \<acute>base1\<ge>0 \<and> \<acute>len1>0 \<and> \<acute>len2>0 \<and> \<acute>len1\<le>\<acute>len2 \<and> 
          (\<acute>base1+\<acute>len1 = \<acute>base2) \<and> (\<acute>base2+\<acute>len2 \<le> length \<acute>a)\<rbrace>
  PROC merge_lo(\<acute>base1, \<acute>len1, \<acute>base2, \<acute>len2)
  \<lbrace>length \<acute>a = length \<^bsup>\<sigma>\<^esup>a\<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (hoare_rule anno="
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
    INV \<lbrace> \<acute>cursor1\<ge>0 \<and> \<acute>cursor2\<ge>\<acute>base2 \<and>
          \<acute>len1>1 \<and> \<acute>len2>0 \<and>
           \<acute>cursor1+\<acute>len1 = \<^bsup>\<sigma>\<^esup>len1 \<and>
           \<acute>cursor2+\<acute>len2 = \<acute>base2+\<^bsup>\<sigma>\<^esup>len2 \<and>
           \<acute>dest+\<acute>len1 = \<acute>cursor2 \<and>
           \<acute>base1 = \<^bsup>\<sigma>\<^esup>base1 \<and>
           \<acute>base2 = \<^bsup>\<sigma>\<^esup>base2 \<and>
           length \<acute>tmp = \<^bsup>\<sigma>\<^esup>len1 \<and>
           length \<acute>a = length \<^bsup>\<sigma>\<^esup>a \<and>
           (\<^bsup>\<sigma>\<^esup>base2+\<^bsup>\<sigma>\<^esup>len2 \<le> length \<^bsup>\<sigma>\<^esup>a) \<rbrace>
    DO
      \<acute>count1 :== 0;;
      \<acute>count2 :== 0;;
      WHILE (\<acute>count1 < \<acute>min_gallop & \<acute>count2 < \<acute>min_gallop)
      INV \<lbrace> \<acute>cursor1\<ge>0 \<and> \<acute>cursor2\<ge>\<acute>base2 \<and>
       \<acute>len1>1 \<and> \<acute>len2>0 \<and>
       \<acute>cursor1+\<acute>len1 = \<^bsup>\<sigma>\<^esup>len1 \<and>
       \<acute>cursor2+\<acute>len2 = \<acute>base2+\<^bsup>\<sigma>\<^esup>len2 \<and>
       \<acute>dest+\<acute>len1 = \<acute>cursor2 \<and>
       \<acute>base1 = \<^bsup>\<sigma>\<^esup>base1 \<and>
       \<acute>base2 = \<^bsup>\<sigma>\<^esup>base2 \<and>
       length \<acute>tmp = \<^bsup>\<sigma>\<^esup>len1 \<and>
       length \<acute>a = length \<^bsup>\<sigma>\<^esup>a \<and>
       (\<^bsup>\<sigma>\<^esup>base2+\<^bsup>\<sigma>\<^esup>len2 \<le> length \<^bsup>\<sigma>\<^esup>a) \<rbrace>
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
      INV \<lbrace> \<acute>cursor1\<ge>0 \<and> \<acute>cursor2\<ge>\<acute>base2 \<and>
      \<acute>len1>1 \<and> \<acute>len2>0 \<and>
      \<acute>cursor1+\<acute>len1 = \<^bsup>\<sigma>\<^esup>len1 \<and>
      \<acute>cursor2+\<acute>len2 = \<acute>base2+\<^bsup>\<sigma>\<^esup>len2 \<and>
      \<acute>dest+\<acute>len1 = \<acute>cursor2 \<and>
      \<acute>base1 = \<^bsup>\<sigma>\<^esup>base1 \<and>
      \<acute>base2 = \<^bsup>\<sigma>\<^esup>base2 \<and>
      length \<acute>tmp = \<^bsup>\<sigma>\<^esup>len1 \<and>
      length \<acute>a = length \<^bsup>\<sigma>\<^esup>a \<and>
      (\<^bsup>\<sigma>\<^esup>base2+\<^bsup>\<sigma>\<^esup>len2 \<le> length \<^bsup>\<sigma>\<^esup>a) \<rbrace>
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
END" in HoarePartial.annotateI)
 apply vcg
         apply (simp_all add:Suc_lessI)
   apply (auto simp add:list_copy_def)
done 




lemma (in merge_hi_impl) merge_hi_spec:
  shows
  "\<forall>\<sigma>. \<Gamma>\<turnstile> \<lbrace> \<sigma>. \<acute>base1\<ge>0 \<and> \<acute>len1>0 \<and> \<acute>len2>0 \<and> \<acute>len1\<ge>\<acute>len2 \<and> 
          (\<acute>base1+\<acute>len1 = \<acute>base2) \<and> (\<acute>base2+\<acute>len2 \<le> length \<acute>a)\<rbrace>
  PROC merge_hi(\<acute>base1, \<acute>len1, \<acute>base2, \<acute>len2)
  \<lbrace>length \<acute>a = length \<^bsup>\<sigma>\<^esup>a \<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (hoare_rule anno="
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
    INV \<lbrace> \<acute>len1>0 \<and> \<acute>len1<\<^bsup>\<sigma>\<^esup>len1 \<and>
       \<acute>len2>1 \<and> \<acute>len2\<le>\<^bsup>\<sigma>\<^esup>len2 \<and>
       \<acute>cursor1+1=\<acute>base1+\<acute>len1 \<and>
       \<acute>cursor2+1=\<acute>len2 \<and>
       \<acute>dest=\<acute>cursor1+\<acute>len2 \<and>
       \<acute>base1 = \<^bsup>\<sigma>\<^esup>base1 \<and>
       \<acute>base2 = \<^bsup>\<sigma>\<^esup>base2 \<and>
       length \<acute>tmp = \<^bsup>\<sigma>\<^esup>len2 \<and>
       length \<acute>a = length \<^bsup>\<sigma>\<^esup>a \<and>
       (\<^bsup>\<sigma>\<^esup>base2+\<^bsup>\<sigma>\<^esup>len2 \<le> length \<^bsup>\<sigma>\<^esup>a) \<and>
       (\<^bsup>\<sigma>\<^esup>base1+\<^bsup>\<sigma>\<^esup>len1 = \<^bsup>\<sigma>\<^esup>base2) \<and>
       length \<acute>a = length \<^bsup>\<sigma>\<^esup>a \<and>
       (\<^bsup>\<sigma>\<^esup>base2+\<^bsup>\<sigma>\<^esup>len2 \<le> length \<^bsup>\<sigma>\<^esup>a)\<rbrace>
    DO
      \<acute>count1 :== 0;;
      \<acute>count2 :== 0;;
      WHILE (\<acute>count1 < \<acute>min_gallop & \<acute>count2 < \<acute>min_gallop)
      INV \<lbrace> \<acute>len1>0 \<and> \<acute>len1<\<^bsup>\<sigma>\<^esup>len1 \<and>
      \<acute>len2>1 \<and> \<acute>len2\<le>\<^bsup>\<sigma>\<^esup>len2 \<and>
       \<acute>cursor1+1=\<acute>base1+\<acute>len1 \<and>
       \<acute>cursor2+1=\<acute>len2 \<and>
       \<acute>dest=\<acute>cursor1+\<acute>len2 \<and>
       \<acute>base1 = \<^bsup>\<sigma>\<^esup>base1 \<and>
       \<acute>base2 = \<^bsup>\<sigma>\<^esup>base2 \<and>
       length \<acute>tmp = \<^bsup>\<sigma>\<^esup>len2 \<and>
       length \<acute>a = length \<^bsup>\<sigma>\<^esup>a \<and>
       (\<^bsup>\<sigma>\<^esup>base2+\<^bsup>\<sigma>\<^esup>len2 \<le> length \<^bsup>\<sigma>\<^esup>a) \<and>
       (\<^bsup>\<sigma>\<^esup>base1+\<^bsup>\<sigma>\<^esup>len1 = \<^bsup>\<sigma>\<^esup>base2)\<and>
       length \<acute>a = length \<^bsup>\<sigma>\<^esup>a \<and>
       (\<^bsup>\<sigma>\<^esup>base2+\<^bsup>\<sigma>\<^esup>len2 \<le> length \<^bsup>\<sigma>\<^esup>a) \<rbrace>
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
      INV \<lbrace> \<acute>len1>0 \<and> \<acute>len1<\<^bsup>\<sigma>\<^esup>len1 \<and>
       \<acute>len2>1 \<and> \<acute>len2\<le>\<^bsup>\<sigma>\<^esup>len2 \<and>
       \<acute>cursor1+1=\<acute>base1+\<acute>len1 \<and>
       \<acute>cursor2+1=\<acute>len2 \<and>
       \<acute>dest=\<acute>cursor1+\<acute>len2 \<and>
       \<acute>base1 = \<^bsup>\<sigma>\<^esup>base1 \<and>
       \<acute>base2 = \<^bsup>\<sigma>\<^esup>base2 \<and>
       length \<acute>tmp = \<^bsup>\<sigma>\<^esup>len2 \<and>
       length \<acute>a = length \<^bsup>\<sigma>\<^esup>a \<and>
       (\<^bsup>\<sigma>\<^esup>base2+\<^bsup>\<sigma>\<^esup>len2 \<le> length \<^bsup>\<sigma>\<^esup>a) \<and>
       (\<^bsup>\<sigma>\<^esup>base1+\<^bsup>\<sigma>\<^esup>len1 = \<^bsup>\<sigma>\<^esup>base2) \<and>
       length \<acute>a = length \<^bsup>\<sigma>\<^esup>a \<and>
       (\<^bsup>\<sigma>\<^esup>base2+\<^bsup>\<sigma>\<^esup>len2 \<le> length \<^bsup>\<sigma>\<^esup>a) \<rbrace>
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
END"
        in HoarePartial.annotateI) 
  apply vcg
  subgoal by (simp add:Suc_diff_Suc)
  subgoal by simp
  subgoal
    apply simp
    using less_imp_diff_less by force
  subgoal by simp
  subgoal by (auto simp add:Suc_diff_Suc)
  subgoal by simp
  subgoal by simp
  done 


end