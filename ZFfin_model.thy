theory ZFfin_model

imports Main ZFfin

begin

theorem not_repl_ext_implies_separ: "\<not> (\<forall> mem. L_repl mem \<and> L_setext mem \<longrightarrow> L_sep mem)"
proof-
  define loop :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where  "loop \<equiv> \<lambda> x y. x = y"
  interpret eq_mem : set_signature loop.
  have loop_ext: "L_setext loop"
    by (unfold_locales, unfold loop_def) force
  have loop_repl: "L_repl loop"
  proof (unfold_locales, rule)
    fix P :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool" and \<Xi>
    assume "\<forall>u. \<exists>!v. P (\<Xi>(0 := u, 1 := v))"
    then show "\<forall>x. \<exists>z. \<forall>v. loop v z = (\<exists>u. loop u x \<and> P (\<Xi>(0 := u, 1 := v)))"
      unfolding loop_def by metis 
  qed
  have SP: "eq_mem.SetFormulaPredicate (\<lambda> \<Xi>. False)"
    by simp
  have "\<not> L_sep loop"
    unfolding L_sep_def using loop_def  SP by blast 
  show ?thesis
    using \<open>\<not> L_sep loop\<close> loop_ext loop_repl by auto
qed
 

section \<open>Permutation models\<close>

locale permutation_model = L_setext_empty_power_union_repl +
  fixes perm
  assumes 
     bij_perm: "bij (perm :: 'a \<Rightarrow> 'a)" and
     SR_fmem: "SetRelation (\<lambda> x y. x \<epsilon> perm y)"

begin

abbreviation perm_mem  (infixr "\<epsilon>\<^sup>f" 51) where
     "perm_mem x y \<equiv> x \<epsilon> perm y"

sublocale L_setext_empty
  by unfold_locales

interpretation pm: L_setext perm_mem
proof (unfold_locales, rule iffI, blast)
  show "x = y" if "\<forall>z. z \<epsilon>\<^sup>f x = z \<epsilon>\<^sup>f y" for x y
    using that[folded setext[of "perm x" "perm y"]] bij_perm
    by (simp add: bij_betw_def inj_eq) 
qed

lemma SFP_fmem[intro]: "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> m \<epsilon>\<^sup>f \<Xi> n)"
  by (rule transform_variables[OF SR_fmem[unfolded SetRelation_def], of "id(0:=m,1:=n)", simplified]) 

(* lemma SR_permmem': "SetRelation (\<lambda>x y. y \<epsilon>\<^sup>f x)" *)
 (* using SR_fmem unfolding SetRelation_def using swap_variables[of "\<lambda> \<Xi>. \<Xi> 0 \<epsilon>\<^sup>f \<Xi> 1" 0 1] by auto *)   

lemma SR_perm_eq: "SetRelation (\<lambda> x y. perm x = y)"
  unfolding SetRelation_def setext logsimps by rule+ 

(* lemma assumes "pm.SetRelation P" shows "SetRelation P" *) 
     (* unfolding SetRelation_def *) 
    (* by (rule pm.SetFormulaPredicate.induct[OF \<open>pm.SetRelation P\<close>[unfolded pm.SetRelation_def]]) *)
       (* (simp_all add: SR_variables[OF SR_fmem]) *)

lemma permSFP_SFP: assumes "pm.SetFormulaPredicate P" shows "SetFormulaPredicate P" 
  by (rule pm.SetFormulaPredicate.induct[OF assms])
  (rule transform_variables[OF SR_fmem[unfolded SetRelation_def], of "id(0:=_,1:=_)", simplified], simp_all) 

lemma perm_model:
  shows "L_setext_empty_power_union_repl perm_mem"
proof
  write pm.subsetM (infix  "\<subseteq>\<^sup>f" 51 ) 
  have finv: "perm ((inv perm) u) = u"  for u
    using bij_perm bij_inv_eq_iff by fast
  have finv': "(inv perm) (perm u) = u"  for u
    using bij_perm bij_inv_eq_iff by metis 
  have inv_iff: "(inv perm) x = y \<longleftrightarrow> perm y = x" for x y
    using bij_perm finv finv' by auto    
  have SR_f': "SetRelation (\<lambda> x y. (inv perm) x = y)"
    using  SR_sym[OF SR_perm_eq, unfolded SR_perm_eq] unfolding inv_iff.  
  have finv_unique: "\<forall>u. \<exists>!v. v = inv perm u"
    using bij_perm by blast
  obtain femp where femp_def: "perm femp  = \<emptyset>"
    using bij_perm bij_pointE by metis 
  show "\<exists>x. \<forall>y. \<not> y \<epsilon>\<^sup>f x"
    using femp_def by (metis empty_is_empty) 
  have fsubset: "x \<subseteq>\<^sup>f y \<longleftrightarrow> (perm x) \<subseteq>\<^sub>M (perm y)" for x y
    unfolding pm.subsetM_def subsetM_def..
  show "\<forall>x. \<exists>y. \<forall>u. u \<epsilon>\<^sup>f y = u \<subseteq>\<^sup>f x"
    unfolding fsubset
  proof
    fix x
    obtain y' where y': "\<And> u. u \<epsilon> y' \<longleftrightarrow> u \<subseteq>\<^sub>M (perm x)"
      using power[rule_format, of "perm x"] by blast
    obtain y where y: "\<And> u. (u \<epsilon> y) = (\<exists>v. v \<epsilon> y' \<and> inv perm v = u)"
      using replf[OF SR_f'[unfolded SetRelation_def], rule_format, of _ y', simplified] by blast 
    have "\<forall>v. (v \<epsilon> perm (inv perm y)) \<longleftrightarrow> perm v \<subseteq>\<^sub>M perm x"
      using y y' bij_perm bij_inv_eq_iff by metis   
    then show "\<exists>y. \<forall>v. (v \<epsilon> perm y) = perm v \<subseteq>\<^sub>M perm x"
      by blast
  qed
  show "\<forall>x. \<exists>y. \<forall>v. v \<epsilon>\<^sup>f y = (\<exists>u. u \<epsilon>\<^sup>f x \<and> v \<epsilon>\<^sup>f u)"
  proof
    fix x
    obtain x' where x': "\<And> u. (u \<epsilon> x') = (\<exists>v. v \<epsilon> perm x \<and>  perm v = u)"
      using replf[OF SR_perm_eq[unfolded SetRelation_def], simplified]  
      using replf[OF SR_f'[unfolded SetRelation_def], rule_format, of _ y', simplified] by blast 
    obtain y where y: "\<And> v. v \<epsilon> y \<longleftrightarrow> (\<exists> u. u \<epsilon> x' \<and> v \<epsilon> u)"
      using union[rule_format, of x'] by blast
    have "\<forall>v. (v \<epsilon> perm (inv perm y)) \<longleftrightarrow> (\<exists>u. u \<epsilon> perm x \<and> v \<epsilon> perm u)"
      using  y x' bij_perm finv by auto   
    then show "\<exists>y. \<forall>v. (v \<epsilon> perm y) = (\<exists>u. u \<epsilon> perm x \<and> v \<epsilon> perm u)"
      by blast
  qed
  fix P \<Xi>
  assume "pm.SetFormulaPredicate P" 
  show "(\<forall>u. \<exists>!v. P (\<Xi>(0 := u, 1 := v))) \<longrightarrow> (\<forall>x. \<exists>z. \<forall>v. v \<epsilon>\<^sup>f z = (\<exists>u. u \<epsilon>\<^sup>f x \<and> P (\<Xi>(0 := u, 1 := v))))"
  proof (rule, rule)
    assume "\<forall>u. \<exists>!v. P (\<Xi>(0 := u, 1 := v))"
    fix x
    have "SetFormulaPredicate P"
      by (simp add: \<open>pm.SetFormulaPredicate P\<close> permSFP_SFP) 
    from replf[rule_format, OF this \<open>\<forall>u. \<exists>!v. P (\<Xi>(0 := u, 1 := v))\<close>[rule_format], of "perm x"]
    obtain z where "\<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> perm x \<and> P (\<Xi>(0 := u, 1 := v)))"
      by blast
    hence "\<forall>v. (v \<epsilon> perm ((inv perm) z)) = (\<exists>u. u \<epsilon> perm x \<and> P (\<Xi>(0 := u, 1 := v)))"
      unfolding finv.
    thus "\<exists>z. \<forall>v. (v \<epsilon> perm z) = (\<exists>u. u \<epsilon> perm x \<and> P (\<Xi>(0 := u, 1 := v))) "
      by blast
  qed
qed

end

section \<open>Regscheme does not follow from reg\<close>

subsection \<open>Permutation regperm\<close>

context L_setext_empty_power_union_repl_reg

begin

fun regperm :: "'a \<Rightarrow> 'a" where
   "regperm a = (if natM a then {a \<union>\<^sub>M {a}\<^sub>M}\<^sub>M else 
                   if (\<exists> b. natM b \<and> a = {b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M) then THE b. a = {b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M else a)"

lemma two_natM: "natM ({\<emptyset>}\<^sub>M \<union>\<^sub>M {{\<emptyset>}\<^sub>M}\<^sub>M)"
  using nat_suc_nat[OF one_natM]. 

lemma suc_sing_not_nat: "\<not> natM ({b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M)"
proof
  assume "natM ({b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M)"
  hence "ordM ({b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M)"
    unfolding natM_def using natM_D1  by blast 
  from ordM_D1[OF this, of "b \<union>\<^sub>M {b}\<^sub>M"]  
  have "b = b \<union>\<^sub>M {b}\<^sub>M"
    unfolding singleton_def' subsetM_def by force
  moreover have "b \<epsilon> b \<union>\<^sub>M {b}\<^sub>M"
    unfolding set_defs by blast
  ultimately show False         
    using mem_not_refl[of b] by simp
qed

lemma regperm_image_nat: assumes "natM a"
  shows "regperm a = {a \<union>\<^sub>M {a}\<^sub>M}\<^sub>M"
  using assms by simp

lemma regperm_image_plus: assumes "natM b"
  shows "regperm ({b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M) = b"
proof-
  have  aux: "(THE c. ({b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M) = ({c \<union>\<^sub>M {c}\<^sub>M}\<^sub>M)) = regperm ({b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M)"
    using \<open>natM b\<close> suc_sing_not_nat by fastforce
  have aux': "{b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M = {x \<union>\<^sub>M {x}\<^sub>M}\<^sub>M \<Longrightarrow> x = b" for x
    using suc_unique[of x b] unfolding setext singleton_def' by blast
  show ?thesis
    using  the_equality[of "\<lambda> c. {b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M = {c \<union>\<^sub>M {c}\<^sub>M}\<^sub>M", OF refl aux']
    unfolding aux by blast    
qed 

lemma regperm_image_else: assumes "\<not> natM a" "\<nexists> b. natM b \<and> a = {b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M"
  shows "regperm a = a"
  using assms by force

lemma regperm_bij: "bij regperm"
proof (rule involuntory_imp_bij)
  fix a
  show "regperm (regperm a) = a"
    by  (cases "natM a", use regperm_image_nat regperm_image_plus in force)
    (cases "\<exists> b. natM b \<and> a = {b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M", use regperm_image_nat regperm_image_plus in metis, auto)
qed

lemma SR_plus[simp]: "SetRelation (\<lambda> x y. y = {x \<union>\<^sub>M {x}\<^sub>M}\<^sub>M)"
  unfolding SetRelation_def by rule

lemma SR_regperm_eq: "SetRelation (\<lambda> x y. regperm x = y)"
proof-
  let ?Def = "\<lambda> x y. (natM x \<and> y = {x \<union>\<^sub>M {x}\<^sub>M}\<^sub>M) \<or> (\<not> natM x \<and> (\<exists> b. natM b \<and> x = {b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M \<and> y = b))
       \<or> (\<not> natM x \<and> (\<nexists>b. natM b \<and> x = {b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M) \<and> y = x)"
  have iff: "?Def x y \<longleftrightarrow> regperm x = y" for x y
  proof-
    consider "natM x" | "\<not> natM x \<and> (\<exists> b. natM b \<and> x = {b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M)" | 
              "\<not> natM x \<and> (\<nexists> b. natM b \<and> x = {b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M)" by blast
    then show ?thesis
      by (cases, force) (use regperm_image_plus in blast, use regperm_image_else in auto)
  qed
  have "SetRelation ?Def"
    unfolding SetRelation_def unfolding logsimps by rule+
  thus ?thesis 
    unfolding iff.
qed

lemma SR_regperm_mem: "SetRelation (\<lambda> x y. x \<epsilon> regperm y)"
proof-
  have "SetRelation (\<lambda> x y. \<exists> z. x \<epsilon> z \<and> regperm y = z)"
    unfolding SetRelation_def logsimps 
    by rule+  (use transform_variables[OF SR_regperm_eq[unfolded SetRelation_def], of "id(0:=1, 1:=_)"] in simp)
  thus ?thesis
    by metis
qed

end

context  L_setext_empty_power_union_repl_reg_fin

begin  

interpretation L_setext_empty_power_repl_reg_tarski
  by unfold_locales

interpretation perm: permutation_model "(\<epsilon>)" regperm
  by unfold_locales (use regperm_bij SR_regperm_mem in blast)+  

abbreviation fmem (infix "\<epsilon>\<^sup>f" 51)  where 
  "fmem x y \<equiv>  perm.perm_mem x y"

interpretation fm: L_setext_empty_power_union_repl fmem
    using perm.perm_model. 

lemma regperm_mem_nat: assumes "natM a"
  shows "u \<epsilon>\<^sup>f a \<longleftrightarrow> u = (a \<union>\<^sub>M {a}\<^sub>M)"
  unfolding regperm_image_nat[OF assms] singleton_def'..

\<comment> \<open>first meta-theorem : not used in the second one\<close>
lemma fmem_not_wf: "\<not> (wfp (\<epsilon>\<^sup>f))"
proof-
  let ?B = "{x . natM x}"
  have "?B \<noteq> {}"
    using Collect_empty_eq one_natM by metis
  moreover have "z \<in> ?B \<Longrightarrow> (z \<union>\<^sub>M {z}\<^sub>M) \<epsilon>\<^sup>f z"  for z
    unfolding mem_Collect_eq using regperm_image_nat unfolding setext singleton_def' by blast
  moreover have "z \<in> ?B \<Longrightarrow> (z \<union>\<^sub>M {z}\<^sub>M) \<in> ?B"  for z
    unfolding mem_Collect_eq using nat_suc_nat.
  ultimately show ?thesis
    unfolding wfp_iff_ex_minimal by metis
qed


\<comment> \<open>the main meta-theorem\<close>
theorem not_regscheme_reg: "\<not> L_regsch (\<epsilon>\<^sup>f)"
proof
  assume "L_regsch (\<epsilon>\<^sup>f)"
  then interpret L_regsch "(\<epsilon>\<^sup>f)"
    by simp
  interpret T: L_setext_empty_union_repl_pair_regsch "(\<epsilon>\<^sup>f)"
    by unfold_locales  
  obtain t where "fm.subsetM \<emptyset> t" "fm.transM t" and least: "\<forall>u. u \<epsilon>\<^sup>f t \<longleftrightarrow> (\<forall>s. fm.subsetM \<emptyset> s \<and> fm.transM s \<longrightarrow> u \<epsilon>\<^sup>f s)"
    using T.transitive_closure_ex by blast
  have trans_t: "z \<epsilon>\<^sup>f t" if  "y \<epsilon>\<^sup>f t" "z \<epsilon>\<^sup>f y" for y z
    using \<open>fm.transM t\<close> that unfolding fm.transM_def fm.subsetM_def by blast
  have suc_t: "u \<union>\<^sub>M {u}\<^sub>M \<epsilon>\<^sup>f t" if "natM u" "u \<epsilon>\<^sup>f t" for u
    using trans_t[OF \<open>u \<epsilon>\<^sup>f t\<close>] using regperm_mem_nat[OF \<open>natM u\<close>] by blast
  have one_in_t: "{\<emptyset>}\<^sub>M \<epsilon>\<^sup>f t"
    using \<open>fm.subsetM \<emptyset> t\<close> unfolding fm.subsetM_def using regperm_mem_nat[OF emp_natM] by simp 
  have two_in_t: "{\<emptyset>}\<^sub>M \<union>\<^sub>M {{\<emptyset>}\<^sub>M}\<^sub>M \<epsilon>\<^sup>f t"
    using trans_t[OF one_in_t] unfolding fm.subsetM_def using regperm_mem_nat[OF one_natM] by simp 
  have "\<not> natM t"
  proof
    assume "natM t"
    have iff: "u \<epsilon>\<^sup>f t \<longleftrightarrow> u = t \<union>\<^sub>M {t}\<^sub>M" for u
      unfolding regperm_image_nat[OF \<open>natM t\<close>] singleton_def'..
    show False
      using two_in_t[unfolded iff, folded one_in_t[unfolded iff]] regperm_mem_nat two_natM
        mem_not_refl setsuc_def' by metis 
  qed
  have "\<nexists> b.  natM b \<and> t = {b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M"
  proof
    assume "\<exists>b. natM b \<and> t = {b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M"
    then obtain b where "natM b" "t = {b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M"
      by blast
    hence iff: "u \<epsilon>\<^sup>f t \<longleftrightarrow> u \<epsilon> b" for u
      using regperm_image_plus by auto
    have "\<emptyset> \<epsilon> b"
      using ordM_trans[OF natM_D1[OF \<open>natM b\<close>] one_in_t[unfolded iff]] unfolding singleton_def'
        (* TODO *)
      by (metis \<open>natM b\<close> \<open>t = {b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M\<close> emp_natM empty_is_empty natM_def one_in_t ordM_total regperm_image_plus)
    have "y \<union>\<^sub>M {y}\<^sub>M \<epsilon> b" if "y \<epsilon> b" for y
      using suc_t[unfolded iff, OF _ that] mem_nat_nat[OF that] \<open>natM b\<close> by blast 
    then show False
      using \<open>\<emptyset> \<epsilon> b\<close> fin by blast
  qed
  have tmem:  "u \<epsilon>\<^sup>f t \<longleftrightarrow> u \<epsilon> t" for u
    by (simp add: \<open>\<nexists>b. natM b \<and> t = {b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M\<close> \<open>\<not> natM t\<close>)
  define tnatM where "tnatM = separationM t natM"
  have tnat:  "u \<epsilon> tnatM \<longleftrightarrow> natM u \<and> u \<epsilon> t" for u
    using separ_def_sp tnatM_def by auto
  show False
    thm notE[OF fin[unfolded not_ex, rule_format]] 
  proof (rule notE[OF fin[unfolded not_ex, rule_format]], rule conjI)
    show "\<emptyset> \<epsilon> tnatM \<union>\<^sub>M {\<emptyset>}\<^sub>M"
      unfolding set_defs by simp 
    show "\<forall>y. y \<epsilon> tnatM \<union>\<^sub>M {\<emptyset>}\<^sub>M \<longrightarrow> y \<union>\<^sub>M {y}\<^sub>M \<epsilon> tnatM \<union>\<^sub>M {\<emptyset>}\<^sub>M"
    proof (rule, rule)
      fix y
      assume "y \<epsilon> tnatM \<union>\<^sub>M {\<emptyset>}\<^sub>M"
      then consider "y = \<emptyset>" | "y \<epsilon> tnatM"
        unfolding set_defs by blast 
      then show "y \<union>\<^sub>M {y}\<^sub>M \<epsilon> tnatM \<union>\<^sub>M {\<emptyset>}\<^sub>M"
      proof (cases) 
        assume "y = \<emptyset>"
        then show ?thesis 
          using one_in_t[unfolded tmem] unfolding binunion_def' tnat by force
      next
        assume "y \<epsilon> tnatM"
        then show ?thesis 
          unfolding tnat  binunion_def' using suc_t[unfolded tmem, of y] nat_suc_nat[of y] by blast
      qed
    qed
  qed
qed

lemma regperm_reg:
  shows "L_setext_empty_power_union_repl_reg (\<epsilon>\<^sup>f)"
proof (unfold_locales, rule, rule)
  fix a
  assume "\<exists>y. y \<epsilon>\<^sup>f a"
  show "\<exists>y. y \<epsilon>\<^sup>f a \<and> (\<forall>v. \<not> (v \<epsilon>\<^sup>f y \<and> v \<epsilon>\<^sup>f a))"
  proof-
    consider "\<exists> n. natM n \<and> n \<epsilon>\<^sup>f a" | "(\<nexists> n. natM n \<and> n \<epsilon>\<^sup>f a) \<and> (\<exists> m. natM m \<and> ({m \<union>\<^sub>M {m}\<^sub>M}\<^sub>M) \<epsilon>\<^sup>f a)" | 
              "(\<nexists> n. natM n \<and> n \<epsilon>\<^sup>f a) \<and> (\<nexists> m. natM m \<and> ({m \<union>\<^sub>M {m}\<^sub>M}\<^sub>M) \<epsilon>\<^sup>f a)" by blast
    then show ?thesis
    proof (cases)
      assume "\<exists> n. natM n \<and> n \<epsilon>\<^sup>f a"
      then obtain k where "natM k" "k \<epsilon>\<^sup>f a" and "\<And> k'. natM k' \<Longrightarrow> k' \<epsilon>\<^sup>f a \<Longrightarrow> \<not> k \<subset>\<^sub>M k'"
        using max_mem[OF _ _ SP_nat, of _ "regperm a"] by fast
      then have max_k: "\<And> k'. natM k' \<Longrightarrow> k' \<epsilon>\<^sup>f a \<Longrightarrow> k' \<noteq> k \<Longrightarrow> k' \<epsilon> k"
        unfolding proper_subset_def' using natM_D1 ordM_D1 ordM_total natM_def by metis 
      show "\<exists>y. y \<epsilon>\<^sup>f a \<and> (\<forall>v. \<not> (v \<epsilon>\<^sup>f y \<and> v \<epsilon>\<^sup>f a))"
      proof (rule exI[of _ k], rule, fact)
        show "\<forall>v. \<not> (v \<epsilon>\<^sup>f k \<and> v \<epsilon>\<^sup>f a)"
        proof (rule, rule)
          fix v 
          assume "v \<epsilon>\<^sup>f k \<and> v \<epsilon>\<^sup>f a"
          hence "v \<epsilon>\<^sup>f a" "v \<epsilon>\<^sup>f k" "v = k \<union>\<^sub>M {k}\<^sub>M"
            unfolding regperm_image_nat[OF \<open>natM k\<close>] singleton_def' by blast+
          show False
            using max_k[of v, OF _ \<open>v \<epsilon>\<^sup>f a\<close>, unfolded \<open>v = k \<union>\<^sub>M {k}\<^sub>M\<close>]
              \<open>natM k\<close> mem_antisym nat_suc_nat pow_setsuc_def' natM_def by blast 
        qed
      qed
    next
      assume "(\<nexists>n. natM n \<and> n \<epsilon>\<^sup>f a) \<and> (\<exists>m. natM m \<and> {m \<union>\<^sub>M {m}\<^sub>M}\<^sub>M \<epsilon>\<^sup>f a)"
      then obtain m where "natM m" "{m \<union>\<^sub>M {m}\<^sub>M}\<^sub>M \<epsilon>\<^sup>f a" "\<nexists>n. natM n \<and> n \<epsilon>\<^sup>f a"
        by blast
      show "\<exists>y. y \<epsilon>\<^sup>f a \<and> (\<forall>v. \<not> (v \<epsilon>\<^sup>f y \<and> v \<epsilon>\<^sup>f a))"
      proof (rule exI[of _ "{m \<union>\<^sub>M {m}\<^sub>M}\<^sub>M"], rule, fact)
        show "\<forall>v. \<not> (v \<epsilon>\<^sup>f {m \<union>\<^sub>M {m}\<^sub>M}\<^sub>M \<and> v \<epsilon>\<^sup>f a)"
          unfolding  regperm_image_plus[OF \<open>natM m\<close>]
          using \<open>\<nexists>n. natM n \<and> n \<epsilon>\<^sup>f a\<close> \<open>natM m\<close> mem_nat_nat by blast
      qed
    next
      assume case3: "(\<nexists>n. natM n \<and> n \<epsilon>\<^sup>f a) \<and> (\<nexists>m. natM m \<and> {m \<union>\<^sub>M {m}\<^sub>M}\<^sub>M \<epsilon>\<^sup>f a)"
      hence "\<not> natM a"
        using nat_suc_nat[of a]
          singleton_def' by force
      have "\<nexists> b. natM b \<and> a = {b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M"
        using case3 \<open>\<exists>y. y \<epsilon>\<^sup>f a\<close> mem_nat_nat regperm_image_plus by metis 
      hence a_mem: "u \<epsilon>\<^sup>f a \<longleftrightarrow> u \<epsilon> a" for u
        using \<open>\<not> natM a\<close> by auto
      have "a \<noteq> \<emptyset>"
        using \<open>\<not> natM a\<close> emp_natM by blast 
      then obtain b where "b \<epsilon> a" "\<forall> v. \<not> (v \<epsilon> b \<and> v \<epsilon> a)"
        using reg by (metis min_subset_ex) 
      have "\<not> natM b" "\<nexists> m. natM m \<and> b = {m \<union>\<^sub>M {m}\<^sub>M}\<^sub>M"
        using \<open>b \<epsilon> a\<close> case3 unfolding a_mem by blast+
      hence b_mem: "u \<epsilon>\<^sup>f b \<longleftrightarrow> u \<epsilon> b" for u
        by auto
      show "\<exists>y. y \<epsilon>\<^sup>f a \<and> (\<forall>v. \<not> (v \<epsilon>\<^sup>f y \<and> v \<epsilon>\<^sup>f a))"
        by (rule exI[of _ b], rule, unfold a_mem b_mem) fact+ 
    qed
  qed
qed

lemma perm_empty: "fm.empty_setM = {{\<emptyset>}\<^sub>M}\<^sub>M"
  by (rule sym, unfold fm.empty_set_def')
  (use binunion_emp emp_natM empty_is_empty regperm_image_plus in metis) 


lemma perm_one: "fm.binunionM fm.empty_setM (fm.singletonM fm.empty_setM) = {{{\<emptyset>}\<^sub>M}\<^sub>M}\<^sub>M"
proof-
  have L: "z \<epsilon>\<^sup>f fm.binunionM fm.empty_setM (fm.singletonM fm.empty_setM) \<longleftrightarrow> z = fm.empty_setM" for z
    unfolding fm.setext fm.binunion_def' fm.singleton_def'
    using fm.nemp_setI fm.pow_setsuc_def' by blast 
  have "z \<epsilon>\<^sup>f {{{\<emptyset>}\<^sub>M}\<^sub>M}\<^sub>M \<longleftrightarrow> z \<epsilon> {{{\<emptyset>}\<^sub>M}\<^sub>M}\<^sub>M" for z
    using singleton_def' binunion_emp mem_nat_nat nat_suc_nat
        regperm_image_else[of "{{{\<emptyset>}\<^sub>M}\<^sub>M}\<^sub>M"] suc_sing_not_nat[of \<emptyset>] by metis
  hence R: "z \<epsilon>\<^sup>f {{{\<emptyset>}\<^sub>M}\<^sub>M}\<^sub>M \<longleftrightarrow> z = fm.empty_setM" for z
    unfolding perm_empty singleton_def'.   
  show ?thesis 
    unfolding fm.setext L R by blast
qed

lemma perm_else_suc_else: assumes "\<not> natM u" "\<nexists> b. natM b \<and> u = {b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M"
  shows "\<not> natM (u \<union>\<^sub>M {u}\<^sub>M)" "\<nexists> b. natM b \<and> u \<union>\<^sub>M {u}\<^sub>M = {b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M"
  using assms by (meson mem_nat_nat setsuc_def') (metis mem_not_refl singleton_def' setsuc_def')   

lemma perm_suc: assumes "\<not> natM u" "\<nexists> b. natM b \<and> u = {b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M"
  shows "fm.binunionM u (fm.singletonM u) = u \<union>\<^sub>M {u}\<^sub>M"
  unfolding fm.setext unfolding fm.binunion_def' regperm_image_else[OF perm_else_suc_else[OF assms]] 
  regperm_image_else[OF assms] binunion_def' singleton_def' fm.singleton_def' by blast

lemma testfin: "L_fin (\<epsilon>\<^sup>f)"
proof(unfold_locales, rule)
  assume "\<exists>x. fm.empty_setM \<epsilon>\<^sup>f x \<and> (\<forall>y. y \<epsilon>\<^sup>f x \<longrightarrow> fm.binunionM y (fm.singletonM y) \<epsilon>\<^sup>f x)"
  then obtain x where xf: "fm.empty_setM \<epsilon>\<^sup>f x" "\<forall>y. y \<epsilon>\<^sup>f x \<longrightarrow> fm.binunionM y (fm.singletonM y) \<epsilon>\<^sup>f x"
    by blast   
  hence mem0: "{{\<emptyset>}\<^sub>M}\<^sub>M \<epsilon>\<^sup>f x" 
    using perm_empty by force
  from xf(2)[rule_format, OF xf(1), unfolded perm_one] 
  have mem1: "{{{\<emptyset>}\<^sub>M}\<^sub>M}\<^sub>M \<epsilon>\<^sup>f x".
  hence not1: "\<not> natM x"
    using mem0 by (metis mem_neq_singleton regperm_mem_nat) 
  have not2: "\<nexists>b. natM b \<and> x = {b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M"
    using mem0 mem1
    by (metis binunion_emp mem_nat_nat regperm_image_plus suc_sing_not_nat)  
  from regperm_image_else[OF not1 not2]
  have x: "{{\<emptyset>}\<^sub>M}\<^sub>M \<epsilon> x" "\<forall>y. y \<epsilon> x \<longrightarrow> fm.binunionM y (fm.singletonM y) \<epsilon> x"
    using xf perm_empty by force+

  let ?P = "\<lambda> u. (\<not> natM u \<and> (\<nexists> b. natM b \<and> (u = {b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M)))"
  have sp: "SetProperty ?P"
    unfolding SetProperty_def set_defs logsimps by rule+
  from sep_sp[OF this, rule_format, of x]
  obtain x' where x': "\<forall>u. (u \<epsilon> x') = (u \<epsilon> x \<and> \<not> natM u \<and> (\<nexists>b. natM b \<and> u = {b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M))"
    by blast
  have "{{{\<emptyset>}\<^sub>M}\<^sub>M}\<^sub>M \<epsilon> x'"
    using mem1  unfolding x'[rule_format] \<open>regperm x = x\<close>
    by (metis binunion_emp mem_nat_nat nat_suc_nat singleton_def' suc_sing_not_nat)
  hence "x' \<noteq> \<emptyset>"
    by force
  have x'_suc: "u \<union>\<^sub>M {u}\<^sub>M \<epsilon> x'" if "u \<epsilon> x'" for u
    unfolding x'[rule_format]
  proof(unfold conj_assoc[symmetric], rule conjI, rule conjI)  
    note u = \<open>u \<epsilon> x'\<close>[unfolded x'[rule_format]]
    have red: "fm.binunionM u (fm.singletonM u) = u \<union>\<^sub>M {u}\<^sub>M"
      by (rule perm_suc) (use  \<open>u \<epsilon> x'\<close>[unfolded x'[rule_format]] in blast)+
    show "u \<union>\<^sub>M {u}\<^sub>M \<epsilon> x"
      by (rule x(2)[rule_format, of u, unfolded red]) (simp add: u)
    show "\<not> natM (u \<union>\<^sub>M {u}\<^sub>M)" "\<nexists>b. natM b \<and> u \<union>\<^sub>M {u}\<^sub>M = {b \<union>\<^sub>M {b}\<^sub>M}\<^sub>M"
      using u perm_else_suc_else by blast+
  qed
  with max_subset_ex[OF \<open>x' \<noteq> \<emptyset>\<close>]   
  show False
    by (metis binunion_def' mem_not_refl proper_subsetM_def singleton_def')
qed     

interpretation find: L_setind "(\<epsilon>\<^sup>f)"
  using L_setext_empty_power_union_repl_reg.fin_implies_setind regperm_reg testfin by blast

end

theorem not_reg_implies_regsch: 
  assumes "L_setext_empty_power_union_repl_reg_fin (m :: 'a \<Rightarrow> 'a \<Rightarrow> bool)"
  shows "\<not> (\<forall> (mem :: 'a \<Rightarrow> 'a \<Rightarrow> bool). L_setext_empty_power_union_repl mem \<and> L_reg mem \<longrightarrow> L_regsch mem)"
proof (rule)
  assume contr: "\<forall>(mem :: 'a \<Rightarrow> 'a \<Rightarrow> bool). L_setext_empty_power_union_repl mem \<and> L_reg mem \<longrightarrow> L_regsch mem"
  interpret L_setext_empty_power_union_repl_reg_fin m
    using assms.
  have  "L_reg fmem"
    using L_setext_empty_power_union_repl_reg_def regperm_reg by blast
  moreover have "\<not> L_regsch fmem"
    using not_regscheme_reg by auto
  moreover have "L_setext_empty_power_union_repl fmem"
    using L_setext_empty_power_union_repl_def L_setext_empty_power_union_repl_reg_def regperm_reg
    by blast
  ultimately show False
    using contr by blast
qed 

theorem not_setind_implies_setindregsch: 
  assumes "L_setext_empty_power_union_repl_reg_fin (m :: 'a \<Rightarrow> 'a \<Rightarrow> bool)"
  shows "\<not> (\<forall> (mem :: 'a \<Rightarrow> 'a \<Rightarrow> bool). L_setext_empty_power_union_repl_reg mem \<and> L_setind mem \<longrightarrow> L_setindregsch mem)"
proof (rule)
  assume contr: "\<forall>(mem :: 'a \<Rightarrow> 'a \<Rightarrow> bool). L_setext_empty_power_union_repl_reg mem \<and> L_setind mem \<longrightarrow> L_setindregsch mem"
  interpret L_setext_empty_power_union_repl_reg_fin m
    using assms.
  have L1: "L_setind fmem"
    using L_setext_empty_power_union_repl_reg.fin_implies_setind regperm_reg testfin by blast
  have L2: "L_setext_empty_power_union_repl_reg fmem"
    using L_setext_empty_power_union_repl_def L_setext_empty_power_union_repl_reg_def regperm_reg
    by blast
  have L3: "L_setindregsch fmem"
    using L1 L2 contr by blast
  interpret i2: L_setext_empty_power_union_repl_reg fmem
    using L2.
  interpret i3: L_setext_empty_setsuc_setindregsch fmem
    using L3 L_setext_empty_setsuc_setindregsch_def i2.L_empty_axioms i2.L_setext_axioms i2.L_setsuc_axioms
    by blast 
  have "L_regsch fmem"
    using i3.L_regsch_axioms by auto  
  then show False
    using not_regscheme_reg by blast
qed 

end