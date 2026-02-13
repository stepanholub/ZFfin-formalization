theory ZFfin_notreg_model

imports Main HereditarilyFinite.Rank ZFfin

begin

text \<open>A model satisfying extensionality, empty set axiom, set successor axiom, and set induction axiom is given by modification of @{term hmem} from @{theory "HereditarilyFinite.HF"}}\<close>

text \<open>Auxiliary\<close>

lemma doubleton_mem_iff[simp]: "a \<^bold>\<in> \<lbrace>x, y\<rbrace> \<longleftrightarrow> a = x \<or> a = y"
  by simp

lemma singleton_hmem_not_one [simp]: "\<lbrace>y\<rbrace> = 1 \<longleftrightarrow> y = 0"
  unfolding One_hf_def by simp

text \<open>Key definition: \<open>0\<close> is a loop violating regularity, \<open>1\<close> is the empty set, and all other naturals code sets as in the Ackermann encoding.\<close>

definition hmem' :: "hf \<Rightarrow> hf \<Rightarrow> bool"  (infixl \<open>\<in>\<^sup>r\<close> 50)
  where "hmem' a b \<longleftrightarrow> (b \<noteq> 1 \<and> a \<^bold>\<in> b) \<or> (a = 0 \<and> b = 0)"

lemma zero_hmem'_iff [simp]: "hmem' a 0 \<longleftrightarrow> a = 0"
  unfolding hmem'_def  by auto

lemma zero_hmem': "(\<forall> a. hmem' a x \<longleftrightarrow> a = 0) \<longleftrightarrow> x = 0"
  by (rule, unfold hmem'_def, metis hsubsetI order_class.order_eq_iff zero_hmem_one) simp

lemma one_hmem': "\<not> (hmem' a 1)"
  by (simp add: hmem'_def)

lemma empty_hmem': "(\<forall> a. \<not> a \<in>\<^sup>r x) \<longleftrightarrow> x = 1"
  by (rule, unfold hmem'_def)
  (meson hf_equalityI hmem_def hmem_hempty, simp add: one_hmem')

interpretation L_setext hmem'
proof (unfold_locales, rule, simp) 
  fix x y
  assume ext: "\<forall>z. (z \<in>\<^sup>r x) = (z \<in>\<^sup>r y)" 
  show "x = y"  
    by (cases "x = 0 \<or> x = 1 \<or> y = 0 \<or> y = 1")
    (metis ext empty_hmem' zero_hmem', use ext[unfolded hmem'_def]
    hf_equalityI in presburger)
qed

interpretation L_empty hmem'
  by (unfold_locales, use one_hmem' in auto) 

interpretation L_setext_empty hmem'
  by unfold_locales

text \<open>Indeed, \<open>1\<close> is now the empty set.\<close>

lemma hmem'_empty: "empty_setM = 1"
  unfolding hf_ext using empty_set_def'[of 1] one_hmem' by simp

text \<open>Modified singletons\<close>

lemma singleton_hmem'_pos: "y \<noteq> 0 \<Longrightarrow> singletonM y = 0 \<triangleleft> y"
  by (unfold singletonM_def, rule collect_def') (unfold hmem'_def One_hf_def, simp)

lemma singleton_hmem'_zero: "singletonM 0 = 0"
  by (simp add: collect_def' singletonM_def)
  
lemma singleton_hmem'_mem:  "u \<in>\<^sup>r singletonM y \<longleftrightarrow> u = y"
  by (cases "y = 0") (simp_all add: singleton_hmem'_zero singleton_hmem'_pos hmem'_def One_hf_def)

text \<open>For sake of successor and induction axioms, the description of modified set-successors is crucial.\<close>

definition setsuc' :: "hf \<Rightarrow> hf \<Rightarrow> hf"  (infixl \<open>\<triangleleft>\<^sup>r\<close> 51)
  where "setsuc' x y =  binunionM x (singletonM y)"

lemma setsuc'_0_0: "\<forall>u. (u \<in>\<^sup>r 0) = (u \<in>\<^sup>r 0 \<or> u = 0)" \<comment> \<open>\<open>0 \<triangleleft>\<^sup>r 0 = 0\<close>\<close>
    unfolding zero_hmem'_iff hmem'_def by simp  

lemma setsuc'_0_y: assumes "y \<noteq> 0" shows "\<forall>u. (u \<in>\<^sup>r \<lbrace>0,y\<rbrace>) = (u \<in>\<^sup>r 0 \<or> u = y)" \<comment> \<open>\<open>0 \<triangleleft>\<^sup>r y = \<lbrace>0,y\<rbrace>\<close>\<close>
proof-
  have "\<lbrace>0, y\<rbrace> \<noteq> 1"
    using assms unfolding One_hf_def hinsert_iff by blast
  thus ?thesis
    unfolding zero_hmem'_iff hmem'_def by (simp add: \<open>\<lbrace>0, y\<rbrace> \<noteq> 1\<close>)
qed

lemma setsuc'_1_0: "\<forall>u. (u \<in>\<^sup>r 0) = (u \<in>\<^sup>r 1 \<or> u = 0)" \<comment> \<open>\<open>1 \<triangleleft>\<^sup>r 0 = 0\<close>\<close>
  by (simp add: one_hmem') 

lemma setsuc'_1_y: assumes "y \<noteq> 0" shows "\<forall>u. (u \<in>\<^sup>r \<lbrace>y\<rbrace>) = (u \<in>\<^sup>r 1 \<or> u = y)" \<comment> \<open>\<open>1 \<triangleleft>\<^sup>r y = \<lbrace>y\<rbrace>\<close>\<close>
   by (simp add: one_hmem' hmem'_def hf_ext[of "\<lbrace>y\<rbrace>"] \<open>y \<noteq> 0\<close>) 

lemma setsuc'_x_y: assumes "x \<noteq> 0" "x \<noteq> 1" shows "\<forall>u. (u \<in>\<^sup>r (x \<triangleleft> y)) = (u \<in>\<^sup>r x \<or> u = y)" \<comment> \<open>\<open>x \<triangleleft>\<^sup>r y = x \<triangleleft> y\<close>\<close>
proof-
  have "x \<triangleleft> y \<noteq> 1"
    unfolding hf_ext  by simp (metis assms(1,2) empty_hmem' hmem'_def zero_hmem') 
  thus ?thesis
    unfolding zero_hmem'_iff hmem'_def  using \<open>x \<noteq> 0\<close> \<open>x \<noteq> 1\<close> by auto
qed

interpretation L_setsuc hmem'
proof (unfold_locales, rule, rule) 
  fix x y :: hf
  consider "x = 0 \<and> y = 0" | "x = 0 \<and> y \<noteq> 0" | "x = 1 \<and> y = 0" | "x = 1 \<and> y \<noteq> 0" | "x \<noteq> 0 \<and> x \<noteq> 1"
    by blast
  then show "\<exists>z. \<forall>u. (u \<in>\<^sup>r z) = (u \<in>\<^sup>r x \<or> u = y)"
    by (cases) 
   (use setsuc'_0_0 in blast,
    use  setsuc'_0_y in blast, 
    use  setsuc'_1_0 in blast, 
    use  setsuc'_1_y in blast, 
    use  setsuc'_x_y in blast) 
qed

text \<open>Once the successor axiom holds, the modified successor behaves as expected.\<close>

lemma setsuc'_def': "\<forall>u. (u \<in>\<^sup>r x \<triangleleft>\<^sup>r y) \<longleftrightarrow> (u \<in>\<^sup>r x \<or> u = y)"
  unfolding setsuc'_def binunionM_def singleton_hmem'_mem
  collect_def_ex[OF setsuc[rule_format]] by blast

text \<open>In mot cases, the modified successor is the same as the original one.\<close>

lemma setsuc_setsuc': assumes "x \<noteq> 0 \<and> x \<noteq> 1"
  shows "x \<triangleleft> y = x \<triangleleft>\<^sup>r y"
     using assms setsuc'_x_y[folded setsuc'_def'[rule_format], folded setext, symmetric, of x] by force


lemma assumes "(\<forall> x. (\<forall> y. y \<^bold>\<in> x \<longrightarrow> P y) \<longrightarrow> P x)"
  shows "P x"
  using assms hmem_induct by blast
       
text \<open>This yields induction.\<close>

interpretation L_setind hmem'
proof (unfold_locales, unfold setsuc'_def[symmetric], rule, rule, rule)
  fix P :: "(nat \<Rightarrow> hf) \<Rightarrow> bool" and w and \<Xi>
  let ?P = "\<lambda> x. P(\<Xi>(0:= x))"
  assume "?P empty_setM" and step: "\<forall>x y. ?P x \<longrightarrow> ?P (x \<triangleleft>\<^sup>r y)"
  hence "?P 1"
    by (simp add: hmem'_empty)
  have "1 \<triangleleft>\<^sup>r 0 = 0"
    by (metis one_hmem' setsuc'_def' zero_hmem')
  hence "?P 0"
    using step[rule_format, OF \<open>?P 1\<close>, of 0] by simp
  show "?P w"
  proof (rule hf_induct[of "\<lambda> x. P(\<Xi>(0:= x))", rule_format])
    show "?P 0"
      by fact
  next
    fix x y
    assume "?P x" "?P y" " y \<^bold>\<notin> x" 
    show "?P (x \<triangleleft> y)"
    proof-
      consider "x = 0 \<and> y = 0" | "x = 0 \<and> y \<noteq> 0" | "x = 1 \<and> y \<noteq> 0" | "x \<noteq> 0 \<and> x \<noteq> 1"
        using \<open>y \<^bold>\<notin> x\<close> by blast
      then show ?thesis
      proof (cases) 
        assume "x = 0 \<and> y = 0"
        hence "x \<triangleleft> y = 1"
          by simp
        then show "?P (x \<triangleleft> y)"
          using \<open>?P 1\<close> by simp
      next
        assume "x = 0 \<and> y \<noteq> 0"
        hence "x \<triangleleft> y = \<lbrace>y\<rbrace>"
          by simp
        then show "?P (x \<triangleleft> y)"
          using setsuc'_1_y[folded setsuc'_def'[rule_format], folded setext, symmetric, of y]
            step[rule_format, OF \<open>?P 1\<close>, of y] \<open>x = 0 \<and> y \<noteq> 0\<close> by force
      next
        assume "x = 1 \<and> y \<noteq> 0"
        hence "x \<triangleleft> y = \<lbrace>0, y\<rbrace>"
          by force
        then show "?P (x \<triangleleft> y)"
          using setsuc'_0_y[folded setsuc'_def'[rule_format], folded setext, symmetric, of y]
            step[rule_format, OF \<open>?P 0\<close>, of y] \<open>x = 1 \<and> y \<noteq> 0\<close> by force
      next
        assume "x \<noteq> 0 \<and> x \<noteq> 1"
        then show "?P (x \<triangleleft> y)"
          using setsuc_setsuc' step[rule_format, OF \<open>?P x\<close>] by force
      qed
    qed
  qed
qed

text \<open>In order to obtain the modified transitive closure of \<open>x\<close>, it is enough to add \<open>0\<close> to \<open>eclose x\<close>\<close>

interpretation L_ts hmem'
proof (unfold_locales, unfold transM_def subsetM_def, rule)
  fix x :: hf
  consider "x = 0" | "x = 1" | "x \<noteq> 0 \<and> x \<noteq> 1"
    by blast
  then show "\<exists>z. (\<forall>y. y \<in>\<^sup>r z \<longrightarrow> (\<forall>za. za \<in>\<^sup>r y \<longrightarrow> za \<in>\<^sup>r z)) \<and>
             (\<forall>za. za \<in>\<^sup>r x \<longrightarrow> za \<in>\<^sup>r z)"
  proof (cases)
    assume "x = 0"
    show ?thesis
      by (rule exI[of _ 0], simp add: \<open>x = 0\<close>) 
  next
    assume "x = 1"
    show ?thesis
      by (rule exI[of _ 1], simp add: \<open>x = 1\<close> one_hmem') 
  next
    assume "x \<noteq> 0 \<and> x \<noteq> 1"
    then have msimp: "\<forall>z. (z \<in>\<^sup>r x) = (z \<^bold>\<in> x)"
      by (simp add: hmem'_def)
    let ?t = "eclose x \<triangleleft> 0" 
    have esimp: "a \<in>\<^sup>r ?t \<longleftrightarrow> a \<^bold>\<in> eclose x \<or> a = 0" for a
    proof  
      assume "a \<in>\<^sup>r eclose x \<triangleleft> 0"
      then show "a \<^bold>\<in> eclose x \<or> a = 0"
        unfolding hmem'_def by blast
    next
      assume "a \<^bold>\<in> eclose x \<or> a = 0" 
      hence "a \<^bold>\<in> eclose x \<triangleleft> 0"
        by blast
      have "eclose x \<triangleleft> 0 \<noteq> 1"
        using \<open>x \<noteq> 0 \<and> x \<noteq> 1\<close>
        by (metis One_hf_def le_eclose less_eq_hempty less_eq_insert2_iff) 
      then show "a \<in>\<^sup>r eclose x \<triangleleft> 0"
        unfolding hmem'_def  using \<open>a \<^bold>\<in> eclose x \<triangleleft> 0\<close> by blast
     qed
    show  "\<exists>z. (\<forall>y. y \<in>\<^sup>r z \<longrightarrow> (\<forall>za. za \<in>\<^sup>r y \<longrightarrow> za \<in>\<^sup>r z)) \<and>
        (\<forall>za. za \<in>\<^sup>r x \<longrightarrow> za \<in>\<^sup>r z)"
    proof (rule exI[of _ ?t], unfold esimp msimp[rule_format], rule, rule, rule)
      fix y assume "y \<^bold>\<in> eclose x \<or> y = 0"
      show "\<forall>z. z \<in>\<^sup>r y \<longrightarrow> z \<^bold>\<in> eclose x \<or> z = 0"
        using Transset_def Transset_eclose \<open>y \<^bold>\<in> eclose x \<or> y = 0\<close> hmem'_def
        by auto
    next
      show "\<forall>z. z \<^bold>\<in> x \<longrightarrow> z \<^bold>\<in> eclose x \<or> z = 0"
        using le_eclose by blast
    qed
  qed
qed

theorem notreg_model: "L_setext_empty (\<in>\<^sup>r)" and "L_setsuc (\<in>\<^sup>r)" and "L_setind (\<in>\<^sup>r)" and "L_ts (\<in>\<^sup>r)" and "\<not> L_reg (\<in>\<^sup>r)"
  by unfold_locales  (metis L_reg.reg zero_hmem'_iff) 

end