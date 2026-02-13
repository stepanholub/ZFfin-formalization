theory ZFfin_HF

imports Main HereditarilyFinite.Rank ZFFin

begin

text \<open>We show that Hereditarily Finite Sets as implemented in @{theory HereditarilyFinite.HF} are a model of 
 ZFfin as implemented in @{theory Draft.ZFfin}\<close>

interpretation zffin: ZFfin "(\<^bold>\<in>)"
  rewrites "zffin.empty_setM = 0" and
           "zffin.singletonM y = \<lbrace>y\<rbrace>" and
           "zffin.binunionM x (zffin.singletonM y) = x \<triangleleft> y"
proof-
  interpret zffin: L_setsuc  "(\<^bold>\<in>)"
    by unfold_locales blast+ 
  interpret zffin: L_empty  "(\<^bold>\<in>)"
    by unfold_locales blast
  interpret zffin: L_setext_empty  "(\<^bold>\<in>)"
    by unfold_locales blast
  show zffin_emp: "zffin.empty_setM = 0"
      using zffin.empty_is_empty by auto
  interpret zffin: L_setsuc  "(\<^bold>\<in>)"
    by unfold_locales blast+ 
  interpret zffin: L_empty  "(\<^bold>\<in>)"
    by unfold_locales blast
  interpret zffin: L_setext_empty_setsuc "(\<^bold>\<in>)"
    by unfold_locales
  show zffin_sing: "zffin.singletonM y = \<lbrace>y\<rbrace>" for y
    using zffin.setsuc_singleton_def' by blast  
  show zffin_suc:  "zffin.binunionM x (zffin.singletonM y) = x \<triangleleft> y" for x y
    using hinsert_eq_sup zffin.binunionM_def zffin_sing sup_hf_def zffin.collectM_def
    by metis
  interpret L_setind "(\<^bold>\<in>)"
  proof
    show "zffin.SetFormulaPredicate P \<Longrightarrow> \<forall>x. P (\<Xi>(0 := zffin.empty_setM)) \<longrightarrow>
        (\<forall>x y. P (\<Xi>(0 := x)) \<longrightarrow> P (\<Xi>(0 := zffin.binunionM x (zffin.singletonM y)))) \<longrightarrow> P (\<Xi>(0 := x))" for P \<Xi>
      unfolding zffin_suc zffin_emp using hf_induct[of "\<lambda> a. P (\<Xi>(0:=a))"] by blast  
  qed
  interpret L_setext_empty_setsuc_setind "(\<^bold>\<in>)"
    by unfold_locales
  interpret L_epsind "(\<^bold>\<in>)"
  proof
    fix \<Xi>  :: "nat \<Rightarrow> hf" and Q
    from Rank.hmem_induct[of "\<lambda> x. Q(\<Xi>(0:=x))"]
    show "(\<forall>x. (\<forall>y. y \<^bold>\<in> x \<longrightarrow> Q (\<Xi>(0 := y))) \<longrightarrow> Q (\<Xi>(0 := x))) \<longrightarrow> (\<forall>x. Q (\<Xi>(0 := x)))"
      by blast
  qed
  show "ZFfin (\<^bold>\<in>)"
  proof (unfold_locales, unfold zffin_emp zffin_suc) 
    fix \<Xi>  :: "nat \<Rightarrow> hf" and P
    from hf_induct[of "\<lambda> x. P(\<Xi>(0:=x))"]
    show "\<nexists>x. 0 \<^bold>\<in> x \<and> (\<forall>y. y \<^bold>\<in> x \<longrightarrow> y \<triangleleft> y \<^bold>\<in> x)"
      using fin zffin_emp zffin_suc by auto
  qed
qed  

end