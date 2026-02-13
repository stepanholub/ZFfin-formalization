(*  Author:     Zuzana Haniková, Czech Academy of Sciences
    Author:     Štěpán Holub, Charles University
*)


theory ZFfin

imports Main
begin

text \<open>In this theory we explore axiomatizations of the theory of hereditarily finite sets, their fragments and relationships between them.\<close>

section Preliminaries

\<comment> \<open>General auxiliary simplifixation rule\<close>
lemma ex_or_iff_or [simp]: "(\<exists>w. (w = x \<or> w = y) \<and> P u w) \<longleftrightarrow> (P u x \<or> P u y)"
   by blast

\<comment> \<open>Purely logical equivalence between B-induction and B-foundation schemes (corresponding instances have negated predicates)\<close>
lemma abstract_foundation_iff: "((\<exists>x. P x) \<longrightarrow> (\<exists>x. P x \<and> B x)) \<longleftrightarrow> (\<forall> x. B x \<longrightarrow> \<not> P x) \<longrightarrow> (\<forall> x. \<not> P x)"
  by auto

section \<open>Signature\<close>

subsection \<open>Membership and basic set-theoretic notions\<close>

locale set_signature =
  fixes membership :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<epsilon>" 50)

begin

text \<open>General relation between regularity scheme and induction scheme. Applying the above remark about B-induction and B-foundation\<close>
thm abstract_foundation_iff[of "\<lambda> x. \<not> P x" "\<lambda> x. (\<forall> y. y \<epsilon> x \<longrightarrow> (P y))", unfolded not_not, symmetric]
thm abstract_foundation_iff[of  "\<lambda> y. P y" "\<lambda> x. (\<forall> y. y \<epsilon> x \<longrightarrow> \<not> (P y))", unfolded not_not]

subsection \<open>Set theoretical notions\<close>

text \<open>We are using Hilbert's description operator \<open>THE\<close> to define sets that 
are defined by its elements. The intended meaning will be provable with appropriate axioms, in particular  extensionality.\<close>

definition subsetM :: "'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<subseteq>\<^sub>M _" [51,51] 53) where
  "subsetM x y \<equiv> (\<forall> z. z \<epsilon> x \<longrightarrow> z \<epsilon> y)"

lemma subsetM_refl[simp]: "x \<subseteq>\<^sub>M x" 
  unfolding subsetM_def by blast

lemma subsetM_trans[simp]: assumes "x \<subseteq>\<^sub>M y" "y \<subseteq>\<^sub>M z" shows "x \<subseteq>\<^sub>M z"
  using assms subsetM_def by simp

definition proper_subsetM :: "'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<subset>\<^sub>M _" [50,50] 50) where
  "proper_subsetM x y \<equiv> (\<forall> z::'a. z \<epsilon> x \<longrightarrow> z \<epsilon> y)  \<and> x \<noteq> y" 

named_theorems set_defs
lemmas[set_defs] = proper_subsetM_def subsetM_def 

lemma proper_subset_def': "x \<subset>\<^sub>M y \<longleftrightarrow> x \<subseteq>\<^sub>M y \<and> x \<noteq> y"
  unfolding set_defs by blast

lemma proper_subsetI: "x \<subseteq>\<^sub>M y \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<subset>\<^sub>M y"
  unfolding set_defs by blast

lemma proper_subsetM_irrefl[simp]: "\<not> x \<subset>\<^sub>M x"
  unfolding set_defs by simp     

definition transM:: "'a \<Rightarrow> bool" where
 "transM x \<equiv> \<forall> y. y \<epsilon> x \<longrightarrow> y \<subseteq>\<^sub>M x "

definition collectM :: "('a \<Rightarrow> bool) \<Rightarrow> 'a"  where
 "collectM Q \<equiv> THE z . (\<forall> u . (u \<epsilon> z \<longleftrightarrow> Q u))"

definition empty_setM ("\<emptyset>") where 
  "empty_setM \<equiv> collectM (\<lambda> x. x \<noteq> x)"

definition separationM :: "'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a" where
 "separationM y Q \<equiv> collectM (\<lambda> u. u \<epsilon> y \<and> Q u)"

definition powersetM :: "'a \<Rightarrow> 'a" ("\<PP>") where
  "powersetM x \<equiv> collectM (\<lambda> u. u \<subseteq>\<^sub>M x)"

definition binunionM :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<union>\<^sub>M" 55) where
  "binunionM x y \<equiv> collectM (\<lambda> u. u \<epsilon> x \<or> u \<epsilon> y)"

definition intersectionM :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("_ \<inter>\<^sub>M _" [55,54] 60) where
  "intersectionM x y \<equiv> collectM (\<lambda> u. u \<epsilon> x \<and> u \<epsilon> y)"

lemma intersection_symm: "x \<inter>\<^sub>M y = y \<inter>\<^sub>M x"
  unfolding intersectionM_def by metis

definition unionM :: "'a \<Rightarrow> 'a" ("\<Union>\<^sub>M")  where
  "unionM x \<equiv> collectM (\<lambda> u. (\<exists> v. v \<epsilon> x \<and> u \<epsilon> v))"

definition differenceM :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (" _ \<setminus>\<^sub>M _") where
  "differenceM x y \<equiv> collectM (\<lambda> u. u \<epsilon> x \<and> \<not> u \<epsilon> y )"

definition singletonM :: "'a \<Rightarrow> 'a" ("{_}\<^sub>M" 70) where
  "singletonM x \<equiv> collectM (\<lambda> u. u = x)"

definition pairM :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("{_,_}\<^sub>M" [51,51] 60) where
  "pairM x y \<equiv> collectM (\<lambda> u. u = x \<or> u = y)"

definition replaceM :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a" where
   "replaceM P x \<equiv> collectM (\<lambda> u. \<exists> v. v \<epsilon> x \<and> P v u)"

definition leastM :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" ("\<Inter>\<^sub>M") where
 "leastM Q \<equiv> collectM (\<lambda> u. \<forall> y. Q y \<longrightarrow> u \<epsilon> y)"

text \<open>Lest transitive superset\<close>
definition leastTS :: "'a \<Rightarrow> 'a" where
  "leastTS x = \<Inter>\<^sub>M (\<lambda> y. transM y \<and> x \<subseteq>\<^sub>M y)"

definition ordered_pairM :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("\<langle>_,_\<rangle>" [51,51] 60) where
  "ordered_pairM a b \<equiv> {{a}\<^sub>M,{a,b}\<^sub>M}\<^sub>M"

definition relationM :: "'a \<Rightarrow> bool" where
  "relationM x \<equiv> \<forall> v. v \<epsilon> x \<longrightarrow> (\<exists> a b. v = \<langle>a,b\<rangle>)"

definition rel_inverseM :: "'a \<Rightarrow> 'a" where
  "rel_inverseM r \<equiv> collectM (\<lambda> u. \<exists> a b. \<langle>a,b\<rangle> \<epsilon> r \<and> u = \<langle>b,a\<rangle>)"

definition functionM :: "'a \<Rightarrow> bool" where
  "functionM x \<equiv> relationM x \<and>  (\<forall> a b c. \<langle>a,b\<rangle> \<epsilon> x \<and> \<langle>a,c\<rangle> \<epsilon> x \<longrightarrow> b = c)"

definition domM :: "'a \<Rightarrow> 'a" where
  "domM r \<equiv> separationM (\<Union>\<^sub>M(\<Union>\<^sub>M r)) (\<lambda> u. \<exists> v. \<langle>u,v\<rangle> \<epsilon> r)"

definition rngM :: "'a \<Rightarrow> 'a" where
  "rngM r \<equiv> separationM (\<Union>\<^sub>M(\<Union>\<^sub>M r)) (\<lambda> u. \<exists> v. \<langle>v,u\<rangle> \<epsilon> r)"

definition one_oneM :: "'a \<Rightarrow> bool" where
  "one_oneM f \<equiv> functionM f \<and>  (\<forall> a b c. \<langle>b,a\<rangle> \<epsilon> f \<and> \<langle>c,a\<rangle> \<epsilon> f \<longrightarrow> b = c)"

lemma one_oneI: assumes "\<forall> v. v \<epsilon> f \<longrightarrow> (\<exists> a b. v = \<langle>a,b\<rangle>)" "(\<forall> a b c. \<langle>b,a\<rangle> \<epsilon> f \<and> \<langle>c,a\<rangle> \<epsilon> f \<longrightarrow> b = c)" "(\<forall> a b c. \<langle>a,b\<rangle> \<epsilon> f \<and> \<langle>a,c\<rangle> \<epsilon> f \<longrightarrow> b = c)"
  shows "one_oneM f"
  using assms unfolding one_oneM_def functionM_def relationM_def by blast+

lemma one_oneD1: "one_oneM f \<Longrightarrow> \<forall> v. v \<epsilon> f \<longrightarrow> (\<exists> a b. v = \<langle>a,b\<rangle>)"
  unfolding one_oneM_def functionM_def relationM_def by blast

lemma one_oneD2: "one_oneM f \<Longrightarrow> (\<forall> a b c. \<langle>b,a\<rangle> \<epsilon> f \<and> \<langle>c,a\<rangle> \<epsilon> f \<longrightarrow> b = c)"
  unfolding one_oneM_def functionM_def relationM_def by blast 

lemma one_oneD3: "one_oneM f \<Longrightarrow> (\<forall> a b c. \<langle>a,b\<rangle> \<epsilon> f \<and> \<langle>a,c\<rangle> \<epsilon> f \<longrightarrow> b = c)"
  unfolding one_oneM_def functionM_def relationM_def by blast

definition set_equivalent :: "'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<approx>\<^sub>M _" [51,51] 52) where
  "set_equivalent x y \<equiv> (\<exists> f. one_oneM f \<and> x = domM f \<and> y = rngM f)"

definition cartesian_productM :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  ("_ \<times>\<^sub>M _ " [51,51] 60) where
  "cartesian_productM x y \<equiv> separationM (\<PP> (\<PP> (x \<union>\<^sub>M y))) (\<lambda> u. \<exists> v\<^sub>1 v\<^sub>2. v\<^sub>1 \<epsilon> x \<and> v\<^sub>2 \<epsilon> y \<and> u = \<langle>v\<^sub>1,v\<^sub>2\<rangle>)"

definition composeM :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("_ \<circ>\<^sub>M _" [51,51] 60) where
  "f \<circ>\<^sub>M g = separationM (domM g \<times>\<^sub>M rngM f) (\<lambda> u. \<exists> a b c. \<langle>a,b\<rangle> \<epsilon> g \<and> \<langle>b,c\<rangle> \<epsilon> f \<and> u = \<langle>a,c\<rangle>)"

definition tarski_fin :: "'a \<Rightarrow> bool" where
   "tarski_fin x \<equiv> \<forall> y. (\<forall> z. z \<epsilon> y \<longrightarrow> z \<subseteq>\<^sub>M x) \<longrightarrow> (\<exists> z. z \<epsilon> y) \<longrightarrow> (\<exists> z. z \<epsilon> y \<and> \<not>(\<exists> w. w \<epsilon> y \<and> z \<subset>\<^sub>M w))"

definition dedekind_fin :: "'a \<Rightarrow> bool" where
   "dedekind_fin x \<equiv> \<forall> y. (y \<subset>\<^sub>M x \<longrightarrow> \<not> x \<approx>\<^sub>M y)"

\<comment> \<open>\<open>x\<close> contains no infinite \<open>\<epsilon>\<close>-decreasing chain as a subset\<close>
definition regular :: "'a \<Rightarrow> bool" where
   "regular x \<equiv> \<forall> y. y \<subseteq>\<^sub>M x \<longrightarrow>  (\<exists> z. z \<epsilon> y) \<longrightarrow> (\<exists> z. z \<epsilon> y \<and> (\<forall> v. \<not> (v \<epsilon> z \<and> v \<epsilon> y)))"

\<comment> \<open>Ordinals and Natural numbers\<close>

definition epschain :: "'a \<Rightarrow> bool" where
  "epschain x \<equiv> transM x \<and> (\<forall> y z. y \<epsilon> x \<and> z \<epsilon> x \<longrightarrow> y \<epsilon> z \<or> y = z \<or> z \<epsilon> y)"

definition ordM :: "'a \<Rightarrow> bool" where
  "ordM x \<equiv> epschain x \<and> regular x"

lemma ordM_regular[simp]: "ordM x \<Longrightarrow> regular x"
  unfolding ordM_def by blast

lemma ordM_D1: "ordM x \<Longrightarrow> y \<epsilon> x \<Longrightarrow> y \<subseteq>\<^sub>M x"
  using ordM_def unfolding transM_def epschain_def by blast

lemma ordM_D2: "ordM x \<Longrightarrow> y \<epsilon> x \<Longrightarrow> z \<epsilon> x \<Longrightarrow> y \<epsilon> z \<or> y = z \<or> z \<epsilon> y"
  using ordM_def epschain_def by blast

definition natM :: "'a \<Rightarrow> bool" where
  "natM x \<equiv> ordM x \<and> tarski_fin x"

definition cardinality :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "cardinality x n \<equiv> natM n \<and> x \<approx>\<^sub>M n"

lemma natM_D1: "natM x \<Longrightarrow> ordM x"
  using natM_def by blast

lemma natM_D2: "natM x \<Longrightarrow> tarski_fin x"
  using natM_def by blast

lemmas[set_defs] = transM_def epschain_def ordM_def tarski_fin_def natM_def functionM_def relationM_def one_oneM_def rngM_def domM_def regular_def cardinality_def set_equivalent_def

subsection \<open>Set relations and properties\<close>

text \<open>We represent set formula by their semantics. A formula is represented by a mapping that assigns truth value to each evaluation of variables. There are countably many variables \<open>x\<^sub>i\<close> represented by natural numbers. That is, an evaluation is a mapping from \<open>nat\<close> to \<open>'a\<close>.

Predicates corresponding to set-formulas are defined inductively.
\<close>

inductive SetFormulaPredicate :: "((nat \<Rightarrow> 'a) \<Rightarrow> bool) \<Rightarrow> bool"
  where 
  SFP_mem[simp]: "\<And> m n. SetFormulaPredicate (\<lambda> \<Xi>. (\<Xi> m) \<epsilon> (\<Xi> n))" \<comment> \<open>formula \<open>x\<^sub>m \<epsilon> x\<^sub>n\<close>\<close>
| SFP_eq[simp]: "\<And> m n. SetFormulaPredicate (\<lambda> \<Xi>. (\<Xi> m) = (\<Xi> n))"  \<comment> \<open>formula \<open>x\<^sub>m = x\<^sub>n\<close>\<close>
| SFP_neg[simp]: "SetFormulaPredicate P \<Longrightarrow> SetFormulaPredicate (\<lambda> \<Xi>. \<not> P \<Xi>)" \<comment> \<open>formula \<open>\<not> \<phi>\<close>\<close>
| SFP_disj[simp]: "SetFormulaPredicate P \<Longrightarrow> SetFormulaPredicate Q 
        \<Longrightarrow> SetFormulaPredicate (\<lambda> \<Xi>. P \<Xi> \<or> Q \<Xi>)"  \<comment> \<open>formula \<open>\<phi> \<or> \<psi>\<close>\<close>
| SFP_all[simp]: "\<And> n. SetFormulaPredicate P \<Longrightarrow> SetFormulaPredicate (\<lambda> \<Xi>. \<forall> a. P (\<Xi>(n:=a)))"
    \<comment> \<open>formula \<open>\<forall> x\<^sub>n. \<phi>\<close>\<close>

text \<open>Every set definable predicate depends on finitely many values. Such values correspond to free variables.\<close>

lemma bounded_free: assumes "SetFormulaPredicate P"
  shows "\<exists> m. \<forall> \<Xi> \<Xi>'. (\<forall> i < m. \<Xi> i = \<Xi>' i) \<longrightarrow>  P(\<Xi>) = P (\<Xi>')"
proof (rule SetFormulaPredicate.induct[OF assms, of "\<lambda> Q. (\<exists> m. \<forall> \<Xi> \<Xi>'. (\<forall> i < m. \<Xi> i = \<Xi>' i) \<longrightarrow>  Q(\<Xi>) = Q (\<Xi>'))"])
  let ?Q = "\<lambda> x. True"
  show "\<exists>max. \<forall>\<Xi> \<Xi>'. (\<forall>i< max. \<Xi> i = \<Xi>' i) \<longrightarrow> (\<Xi> m \<epsilon> \<Xi> n) = (\<Xi>' m \<epsilon> \<Xi>' n)" for m n :: nat
    by (rule exI[of _ "Suc(max m n)"]) force   
  show "\<exists>max. \<forall>\<Xi> \<Xi>'. (\<forall>i< max. \<Xi> i = \<Xi>' i) \<longrightarrow> (\<Xi> m = \<Xi> n) = (\<Xi>' m = \<Xi>' n)" for m n :: nat
    by (rule exI[of _ "Suc(max m n)"]) force   
next
  fix Q :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool"
  assume "\<exists>m. \<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> Q \<Xi> = Q \<Xi>'"
  then obtain m where "\<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> Q \<Xi> = Q \<Xi>'"
    by blast
  then have "\<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> (\<not> Q \<Xi>) = (\<not> Q \<Xi>')" 
    by simp
  thus "\<exists>m. \<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> (\<not> Q \<Xi>) = (\<not> Q \<Xi>')"
    by blast
next
  fix Q R :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool"
  assume "\<exists>m. \<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> Q \<Xi> = Q \<Xi>'" "\<exists>m. \<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> R \<Xi> = R \<Xi>'"
  then obtain max_Q max_R where "\<forall>\<Xi> \<Xi>'. (\<forall>i<max_Q. \<Xi> i = \<Xi>' i) \<longrightarrow> Q \<Xi> = Q \<Xi>'" "\<forall>\<Xi> \<Xi>'. (\<forall>i<max_R. \<Xi> i = \<Xi>' i) \<longrightarrow> R \<Xi> = R \<Xi>'"
    by blast
  hence "\<forall>\<Xi> \<Xi>'. (\<forall>i<(max max_Q max_R). \<Xi> i = \<Xi>' i) \<longrightarrow> (Q \<Xi> \<or> R \<Xi>) = (Q \<Xi>' \<or> R \<Xi>')"
    unfolding less_max_iff_disj by metis
  thus "\<exists>m. \<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> (Q \<Xi> \<or> R \<Xi>) = (Q \<Xi>' \<or> R \<Xi>')"
    by blast
next
  fix Q :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool" and n :: nat
  assume "\<exists>m. \<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> Q \<Xi> = Q \<Xi>'"
  then obtain max where max: "(\<forall>i<max. \<Xi> i = \<Xi>' i) \<longrightarrow> Q \<Xi> = Q \<Xi>'" for \<Xi> \<Xi>'
    by blast
  have "(\<forall>i<max. \<Xi> i = \<Xi>' i) \<longrightarrow> (\<forall>a. Q (\<Xi>(n := a))) = (\<forall>a. Q (\<Xi>'(n := a)))" for \<Xi> \<Xi>'
    using max[of "\<Xi>(n := _)" "\<Xi>'(n := _)"] by force
  thus "\<exists>m. \<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> (\<forall>a. Q (\<Xi>(n := a))) = (\<forall>a. Q (\<Xi>'(n := a)))"  
    by blast
qed

\<comment>\<open>Renaming variables in any way (not necessarily permuting them) preserves set predicate.\<close>
lemma transform_variables: assumes "SetFormulaPredicate P"
  shows "SetFormulaPredicate (\<lambda> \<Xi>. P (\<lambda> n. \<Xi>(f n)))"
  using assms
proof(induction arbitrary: f rule:  SetFormulaPredicate.inducts)
  case (SFP_mem m n)
  then show ?case 
    using set_signature.SFP_mem by blast
next
  case (SFP_eq m n)
  then show ?case 
    using set_signature.SFP_eq  by blast
next
  case (SFP_neg P)                       
  then show ?case
    using SetFormulaPredicate.SFP_neg  by simp 
next
  case (SFP_disj P Q)
  then show ?case using SetFormulaPredicate.SFP_disj by simp
next
  case (SFP_all P n)
  then show ?case
  proof-
    obtain k  where k: "(\<forall>i < k. \<Xi> i = \<Xi>' i) \<Longrightarrow> P \<Xi> = P \<Xi>'" for \<Xi> \<Xi>' :: "nat \<Rightarrow> 'a"
      using bounded_free[OF \<open>SetFormulaPredicate P\<close>] by blast
    have "\<exists> M. n < M \<and> (\<forall> b < k. f b < M)"
    proof (induction k, rule exI[of _ "max n (f 0) + 1"], force)
      case (Suc k)
      obtain M where M: "n < M" "\<forall>b < k. f b < M"
        using Suc.IH by blast
      show "\<exists>M>n. \<forall>b<Suc k. f b < M"
        by (rule exI[of _ "Suc (max M (f k))"])
        (metis M le_imp_less_Suc less_SucE less_SucI less_max_iff_disj max.cobounded2) 
      qed
    then obtain M where M_bound: "n < M" "(\<forall> b < k. f b < M)"
      by blast  
    have M: "(\<forall>i < M. \<Xi> i = \<Xi>' i) \<Longrightarrow> (\<lambda>\<Xi>. P ((\<lambda>b. \<Xi> (f b))(n:=a))) \<Xi> = (\<lambda>\<Xi>'. P ((\<lambda>b. \<Xi>' (f b))(n:=a))) \<Xi>'" for \<Xi> \<Xi>' :: "nat \<Rightarrow> 'a" and a
      by (rule k[of "(\<lambda>b. \<Xi> (f b))(n := a)" "(\<lambda>b. \<Xi>' (f b))(n := a)"]) (use M_bound in auto) 
    have fsimp: "(\<lambda>b. (\<Xi>(p := a)) ((f(n := p)) b)) = (\<lambda>b. (\<Xi>(p := a)) (f b))(n:=a)"  for \<Xi> :: "nat \<Rightarrow> 'a"  and a p
      by auto
    have M_irrelevant: "P ((\<lambda>b. (\<Xi>(M := a)) (f b))(n := a)) =  P ((\<lambda>b. \<Xi> (f b))(n := a))" for \<Xi> a
      by (rule M) simp
    show ?thesis
      using set_signature.SFP_all[OF SFP_all(2)[of "f(n:=M)"], of M]
      unfolding fsimp M_irrelevant. 
  qed
qed

lemma update_variable[intro]: assumes "SetFormulaPredicate P"
  shows "SetFormulaPredicate (\<lambda> \<Xi>. P(\<Xi>(n:= \<Xi> m)))"
proof-
  have aux: "(\<lambda> a. \<Xi> ((id(n:=m)) a)) = (\<Xi> (n:=\<Xi> m))" for \<Xi> :: "nat \<Rightarrow> 'a"
    by force
  show ?thesis
    by (rule transform_variables[OF assms, of "id (n:=m)", unfolded aux]) 
qed

lemma swap_variables: assumes "SetFormulaPredicate P"
  shows "SetFormulaPredicate (\<lambda> \<Xi>. P (\<Xi>(k := \<Xi> l, l := \<Xi> k)))"
proof-
  have "(\<lambda>n. \<Xi> ((id(k := l, l := k)) n)) = \<Xi>(k := \<Xi> l, l := \<Xi> k)" for \<Xi> :: "nat \<Rightarrow> 'a"
    by fastforce
  from transform_variables[OF assms, of "id(k:=l,l:=k)", unfolded this]
  show ?thesis.
qed

text \<open>A rule allowing to get rid of quantifiers when proving that a formula defines \<open>SetFormulaPredicate\<close>\<close>

lemma sfp_all_rule4 [intro]: assumes "\<And> m. SetFormulaPredicate (\<lambda> \<Xi>. Q (\<Xi> m) (\<Xi> k1) (\<Xi> k2) (\<Xi> k3) (\<Xi> k4))" 
  shows "SetFormulaPredicate (\<lambda> \<Xi>. \<forall> y. Q y (\<Xi> k1) (\<Xi> k2) (\<Xi> k3) (\<Xi> k4))"
  using SFP_all[OF assms, of "k1+k2+k3+k4+1" "k1+k2+k3+k4+1"] by simp

named_theorems logsimps
lemmas[logsimps] = not_not
lemma reduce_ex [logsimps]: "(\<lambda>\<Xi>. (\<exists>z. Q z \<Xi>)) = (\<lambda>\<Xi>. \<not> (\<forall> z. \<not> (Q z \<Xi>)))"
  by blast
lemma reduce_and [logsimps]: "(\<lambda> \<Xi>. (P \<Xi>) \<and> (Q \<Xi>)) = (\<lambda> \<Xi>. (\<not> ((\<not> (P \<Xi>)) \<or> (\<not> (Q \<Xi>)))))"
  by blast
lemma reduce_imp[logsimps]: "(\<lambda> \<Xi>. (P \<Xi>) \<longrightarrow> (Q \<Xi>)) = (\<lambda> \<Xi>. (\<not> (P \<Xi>) \<or> (Q \<Xi>)))"
  by blast
lemma reduce_iff[logsimps]: "(\<lambda> \<Xi>. (P \<Xi>) \<longleftrightarrow> (Q \<Xi>)) = (\<lambda>\<Xi>. \<not> (\<not> (\<not> P \<Xi> \<or> Q \<Xi>) \<or> \<not> (\<not> Q \<Xi> \<or> P \<Xi>)))"
  unfolding iff_conv_conj_imp unfolding logsimps  by blast
  
lemma SFP_const[intro,simp]: "SetFormulaPredicate (\<lambda>\<Xi>. b)"
  by (induct b) (use SFP_eq[of 0 0] SFP_neg[OF SFP_eq[of 0 0]] in force)+ 

lemma SFP_ex: assumes "SetFormulaPredicate P" shows "SetFormulaPredicate (\<lambda> \<Xi>. (\<exists> z. P (\<Xi> (m := z))))"
  unfolding logsimps by (rule SFP_neg, rule SFP_all, rule SFP_neg, fact)

lemma SFP_replace: assumes "SetFormulaPredicate P" and free_m: "\<forall> \<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow>  P \<Xi> = P \<Xi>'"
  shows "SetFormulaPredicate(\<lambda>\<Xi>. \<exists>z. \<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> \<Xi> m \<and> P (\<Xi> (0:=u,1:=v))))"
proof-
  let ?f = "id(0:= m+1, 1:= m+2)"
  let ?P = "\<lambda> \<Xi>. P (\<Xi>(0 := \<Xi>(m+1),1:=\<Xi>(m+2)))"
  have idsimp: "(\<lambda>n. \<Xi> (?f n)) = \<Xi> (0:= \<Xi>(m+1),1 :=\<Xi>(m+2))" for \<Xi> :: "nat \<Rightarrow> 'a" by fastforce
  have Psimp: "P (\<Xi>(m + 3 := z, m + 2 := v, m + 1 := u, 0 := (\<Xi>(m + 3 := z, m + 2 := v, m + 1 := u)) (m + 1),1 := (\<Xi>(m + 3 := z, m + 2 := v, m + 1 := u)) (m + 2))) 
    = P (\<Xi> (0:=u,1:=v))" for \<Xi> v u z 
    by (rule free_m[rule_format]) force    
  have sfp: "SetFormulaPredicate ?P"
    using transform_variables[OF assms(1), of ?f] unfolding idsimp.
  have "SetFormulaPredicate (\<lambda>\<Xi>. \<not> \<Xi> (m+1) \<epsilon> \<Xi> m \<or> \<not> ?P \<Xi>)"
    by rule+ fact
  from SFP_all[OF this, of "m+1", simplified fun_upd_same fun_upd_other]
  have "SetFormulaPredicate (\<lambda>\<Xi>. \<forall>z. \<not> z \<epsilon> \<Xi> m \<or> \<not> ?P (\<Xi>(m + 1 := z)))"
    unfolding logsimps by simp
  have "SetFormulaPredicate (\<lambda> \<Xi>. (\<Xi> (m+2) \<epsilon> \<Xi> (m+3)) = (\<exists>u. u \<epsilon> \<Xi> m \<and> ?P (\<Xi>(m+1 := u))))"
    unfolding logsimps by (rule | fact)+
  from SFP_all[OF this, of "m+2", simplified fun_upd_same fun_upd_other]
  have "SetFormulaPredicate (\<lambda>\<Xi>. \<forall>a. (a \<epsilon> \<Xi> (m + 3)) = (\<exists>u. u \<epsilon> \<Xi> m \<and> ?P (\<Xi>(m + 2 := a, m + 1 := u))))" by simp
  note aux = SFP_all[OF SFP_neg[OF this], of "m+3", simplified fun_upd_same fun_upd_other]
  have " SetFormulaPredicate
   (\<lambda>\<Xi>. \<exists> z. (\<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> \<Xi> m \<and> ?P (\<Xi>(m + 3 := z, m + 2 := v, m + 1 := u)))))"
    unfolding logsimps using SFP_neg[OF aux[unfolded logsimps]] by simp  
  then show "SetFormulaPredicate (\<lambda>\<Xi>. \<exists>z. \<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> \<Xi> m \<and> P (\<Xi>(0 := u, 1 := v))))"
    unfolding Psimp.
qed


text \<open>A relation is set-definable, if the predicate it defines by assigning values to variables \<open>x\<^sub>0\<close> and \<open>x\<^sub>1\<close> is set-definable. The value of the predicate therefore cannot depend on other variables than \<open>x\<^sub>0\<close> and \<open>x\<^sub>1\<close>. In other words, if a formula \<open>\<phi>\<close> defining a set-definable relation contains a free variable \<open>x\<^sub>k, 1 < k\<close>, then it is equivalent to \<open>\<forall> x\<^sub>k. \<phi>\<close> \<close>

definition SetRelation :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where
   "SetRelation P \<equiv> SetFormulaPredicate (\<lambda> \<Xi>. P (\<Xi> 0) (\<Xi> 1))"


text \<open>A set-definable property is defined similarly.\<close>

definition SetProperty :: "('a \<Rightarrow>  bool) \<Rightarrow> bool"
  where
   "SetProperty P \<equiv> SetFormulaPredicate (\<lambda> \<Xi>. P (\<Xi> 0))"

subsubsection \<open>Auxiliary proofs for specific useful set-relations and set-properties\<close>

lemma SR_neg[simp, intro]: "SetRelation P \<Longrightarrow> SetRelation (\<lambda> x y. \<not> P x y)"
  unfolding SetRelation_def by rule

lemma SR_sym[simp, intro]: assumes "SetRelation P" shows "SetRelation (\<lambda> x y. P y x)"
  using swap_variables[OF assms[unfolded SetRelation_def], of 0 1, simplified fun_upd_same fun_upd_other]
  unfolding SetRelation_def.

lemma SP_const[simp]: "SetProperty (\<lambda> x. b)"
  unfolding SetProperty_def using SFP_const.
     
lemma SP_neg[simp, intro]: "SetProperty P \<Longrightarrow> SetProperty (\<lambda> x. \<not> P x)"
  unfolding  SetProperty_def using SFP_neg. 

lemma SP_tarski[simp]: "SetProperty tarski_fin"
  unfolding SetProperty_def by (unfold logsimps set_defs) rule+

lemma SFP_nat[intro,simp]: "SetFormulaPredicate (\<lambda> \<Xi>. natM  (\<Xi> k))"
  unfolding logsimps set_defs by rule+

lemma SP_nat[simp]: "SetProperty natM"
  unfolding SetProperty_def by rule

end

section \<open>Axiomatizations of finite sets\<close>

subsection \<open>Finiteness axioms\<close>

locale L_fin = set_signature + 
   assumes fin: "\<not> (\<exists> x. \<emptyset> \<epsilon> x \<and> (\<forall> y. y \<epsilon> x \<longrightarrow> y \<union>\<^sub>M {y}\<^sub>M \<epsilon> x))"

locale L_setind = set_signature +
  assumes setind: "\<And> P. SetFormulaPredicate P \<Longrightarrow> 
    P(\<Xi>(0:= \<emptyset>)) \<longrightarrow> (\<forall> x y. P(\<Xi>(0:= x)) \<longrightarrow> P (\<Xi>(0:= x\<union>\<^sub>M{y}\<^sub>M))) \<longrightarrow> (\<forall> x. P(\<Xi>(0:= x)))"
begin

lemma setind_SP:   assumes "SetProperty P" "P \<emptyset>" and step:  "\<forall> x y. P x \<longrightarrow> P (x\<union>\<^sub>M{y}\<^sub>M)"
  shows  "P x"
  using setind[of "\<lambda> \<Xi>. P (\<Xi> 0)", folded SetProperty_def, OF assms(1), simplified] \<open>P \<emptyset>\<close> step by blast  

lemma setind_var:   assumes "SetFormulaPredicate P" "P(\<Xi>(n:= \<emptyset>))" and step: "\<forall> x y. P(\<Xi>(n:= x)) \<longrightarrow> P (\<Xi>(n:= x\<union>\<^sub>M{y}\<^sub>M))"
  shows "P(\<Xi>(n:= x))"
proof-
  from bounded_free[OF \<open>SetFormulaPredicate P\<close>]
  obtain m where m: "P \<Xi> = P \<Xi>'" if "\<forall>i<m. \<Xi> i = \<Xi>' i" for \<Xi> \<Xi>'
    by blast
  let ?m = "Suc (n + m)"  
  let ?f = "id(0 := ?m, n:= 0)"
  let ?Q = "\<lambda> X. (P (\<lambda> b. X (?f  b)))"
  let ?X = "\<Xi>(?m:= \<Xi> 0)" 
  have sfpq:  "SetFormulaPredicate ?Q"
    using transform_variables[OF \<open>SetFormulaPredicate P\<close>] by simp
  have small: "\<forall> i < m. (\<Xi>(n := u)) i = (?X (0 := u)) (?f i)" for u
    by auto
  have equiv: "(P (\<Xi>(n := u))) \<longleftrightarrow> (?Q (?X (0 := u)))" for u
    by (rule m[of "\<Xi>(n := u)" "\<lambda> b. (?X (0 := u))(?f b)"]) fact
  show ?thesis
   unfolding equiv
   by (rule setind[rule_format, OF sfpq, of "\<Xi>(Suc (n + m) := \<Xi> 0)"], unfold equiv[symmetric])
   (use assms in blast)+    
qed

end

locale L_dedekind = set_signature + 
   assumes dedekind: "\<forall> x. dedekind_fin x"

locale L_tarski = set_signature + 
  assumes tarski: "\<forall> y. tarski_fin y"

subsection Extensionality

locale L_setext = set_signature +
  assumes setext: "x = y \<longleftrightarrow> (\<forall> z. z \<epsilon> x \<longleftrightarrow> z \<epsilon> y)"

begin

text \<open>set in HOL is defined as a class. Therefore, the following comprehension is an axiom.\<close>
lemma "x \<in> {u. P u} \<longleftrightarrow> P x"
   using mem_Collect_eq.

text \<open>In case of our sets, only uniqueness, not existence is guaranteed.\<close>

lemma collect_def': 
  assumes "\<forall> u. (u \<epsilon> w \<longleftrightarrow> Q u)"
  shows "collectM Q = w"
proof-
  let ?P = "\<lambda> z. (\<forall> u. u \<epsilon> z \<longleftrightarrow> Q u)"
  have unique: "z' = w" if "?P z'" for z'
    unfolding setext[rule_format, of z' w] 
    using that assms by blast
  then show ?thesis
    using theI[of ?P w, OF assms unique] unfolding collectM_def by blast 
qed

lemma collect_def_ex: \<comment> \<open>A formulation useful in proofs\<close>
  assumes "\<exists> w. \<forall> u . (u \<epsilon> w \<longleftrightarrow> Q u)"
  shows "u \<epsilon> collectM Q \<longleftrightarrow> Q u"
  using assms collect_def' assms by auto

lemma proper_subset_diff[simp] : "y \<subset>\<^sub>M x \<Longrightarrow> \<exists> z. z \<epsilon> x \<and> \<not> z \<epsilon> y" 
  unfolding proper_subsetM_def setext by blast

lemma subsetM_antisym: "y \<subseteq>\<^sub>M x \<Longrightarrow> x \<subseteq>\<^sub>M y \<Longrightarrow> x = y" 
  unfolding subsetM_def setext by blast

lemma proper_subsetM_trans[simp]: assumes "x \<subset>\<^sub>M y" "y \<subset>\<^sub>M z" shows "x \<subset>\<^sub>M z"
proof (unfold proper_subsetM_def, rule)
  show "(\<forall> u. u \<epsilon> x \<longrightarrow> u \<epsilon> z)"
    using assms proper_subsetM_def by simp
  show "x \<noteq> z"
    by (rule notI) (use assms proper_subsetM_def  setext[of z y] in auto)
qed

end                                                        
                                             
subsection Empty_set  

locale L_empty = set_signature + 
  assumes empty: "\<exists> x. \<forall> y. (\<not> y \<epsilon> x)"

locale L_setext_empty = L_setext + L_empty

begin

lemma empty_is_empty[simp]: "\<forall> y. (\<not> y \<epsilon> \<emptyset>)"
proof-
  have ex: "\<exists> x. \<forall> z. z \<epsilon> x \<longleftrightarrow> z \<noteq> z"
    using empty by auto
  from collect_def_ex[OF this, folded empty_setM_def]
  show ?thesis 
    unfolding empty_setM_def collectM_def by auto
qed

lemma empty_set_def'[set_defs]: "x = \<emptyset> \<longleftrightarrow> (\<forall> u. \<not> u \<epsilon> x)"
  unfolding setext by simp

lemma empty_mem_false [set_defs]: "u \<epsilon> \<emptyset> \<longleftrightarrow> False"
  using empty_set_def'  by simp

lemma SFP_empty_n [simp]: "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> n = \<emptyset>)"
  unfolding SetProperty_def by (unfold logsimps set_defs) rule+

lemma SP_empty[simp]: "SetProperty (\<lambda>x. x = \<emptyset>)"
  unfolding SetProperty_def by simp

lemma SFP_empty_n' [simp]: "SetFormulaPredicate (\<lambda>\<Xi>. \<forall>u. \<not> u \<epsilon> \<Xi> n)"
  using SFP_empty_n empty_set_def' by simp

lemma empty_dedekind[simp]: shows "dedekind_fin \<emptyset>"
  unfolding dedekind_fin_def set_defs by auto

lemma nemp_setI[intro]: "x \<epsilon> y \<Longrightarrow> y \<noteq> \<emptyset>"
  by force

lemma nemp_setI_ex: "\<exists> x. x \<epsilon> y \<Longrightarrow> y \<noteq> \<emptyset>"
  by force

lemma empty_is_subset: "\<emptyset> \<subseteq>\<^sub>M A"
  unfolding subsetM_def by force

lemma subset_of_empty[simp]: "u \<subseteq>\<^sub>M \<emptyset> \<longleftrightarrow> u = \<emptyset>"
  unfolding subsetM_def empty_set_def' by simp

lemma empty_regular[simp]: "regular \<emptyset>"
  unfolding regular_def by simp

lemma empty_tarski[simp]: "tarski_fin \<emptyset>"
  unfolding tarski_fin_def subset_of_empty proper_subsetM_def using empty_set_def' by blast

lemma empty_trans[simp]: "transM \<emptyset>"
  unfolding transM_def by simp

lemma emp_natM[simp]: "natM \<emptyset>"
  by (simp add: natM_def ordM_def epschain_def) 

end

subsection Regularity

locale  L_reg = set_signature +
  assumes reg: "\<forall> x. (\<exists> y. y \<epsilon> x) \<longrightarrow> (\<exists> y. y \<epsilon> x \<and> (\<forall> v. \<not> (v \<epsilon> y \<and> v \<epsilon> x)))"

begin

lemma any_reg[simp]: "regular x"
  using reg unfolding regular_def by blast

text \<open>Note that \<open>\<not> x \<epsilon> x\<close> cannot be proved without existence of a singleton.\<close>

end

lemma (in set_signature) reg_all_regular_iff:
  "L_reg (\<epsilon>) \<longleftrightarrow> (\<forall> x. regular x)"
proof
  assume "L_reg (\<epsilon>)"
  then interpret L_reg "(\<epsilon>)".
  show "\<forall> x. regular x"
    using reg unfolding regular_def by blast
next
  assume all_reg: "\<forall> x. regular x"
  show "L_reg (\<epsilon>)"
    by unfold_locales (meson all_reg regular_def set_signature.subsetM_refl)  
qed


locale L_regsch = set_signature + 
  assumes regsch: "SetFormulaPredicate P \<Longrightarrow> (\<exists> x. P (\<Xi> (0:=x))) \<longrightarrow>  (\<exists> x. P (\<Xi> (0:=x)) \<and> (\<forall> y. y \<epsilon> x \<longrightarrow> \<not> P (\<Xi> (0:=y))))"

begin

lemma regsch_epsind:
   "SetFormulaPredicate Q \<Longrightarrow> (\<forall> x. (\<forall>y. (y \<epsilon> x \<longrightarrow> Q (\<Xi> (0:=y))))  \<longrightarrow>  Q (\<Xi> (0:=x))) \<longrightarrow>  (\<forall> x. Q (\<Xi> (0:=x)))"
  using regsch[of "\<lambda> x. \<not> Q x" \<Xi>] using SFP_neg by blast 

lemma regsch_mem_not_refl: "\<not> u \<epsilon> u"
proof
  assume "u \<epsilon> u"
  hence ex: "\<exists>x. (undefined(1 := u, 0 := x)) 0 = (undefined(1 := u, 0 := x)) 1"
    by force
  have sfp: "SetFormulaPredicate (\<lambda>\<Xi>. (\<Xi> 0) = (\<Xi> 1))"
    by rule
  from regsch[of "\<lambda> \<Xi>. (\<Xi> 0) = (\<Xi> 1)", rule_format, OF sfp ex]
  show False
    using \<open>u \<epsilon> u\<close> by auto
qed

sublocale L_reg \<comment> \<open>regsch is stronger than normal regularity\<close>
  by unfold_locales (use regsch[of "\<lambda>\<Xi>. \<Xi> 0 \<epsilon> \<Xi> 1", simplified] in fast)

end 

locale L_epsind = set_signature + 
  assumes epsind: "SetFormulaPredicate Q \<Longrightarrow> (\<forall> x. (\<forall>y. (y \<epsilon> x \<longrightarrow> Q (\<Xi> (0:=y))))  \<longrightarrow>  Q (\<Xi> (0:=x))) \<longrightarrow>  (\<forall> x. Q (\<Xi> (0:=x)))"

begin

lemma epsind_regsch: assumes "SetFormulaPredicate P" "\<exists> x. P (\<Xi> (0:=x))" 
  shows "\<exists> x. P (\<Xi> (0:=x)) \<and> (\<forall> y. y \<epsilon> x \<longrightarrow> \<not> P (\<Xi> (0:=y)))"   
proof-
  have SP: "SetFormulaPredicate (\<lambda> x. \<not> P x)"
    using \<open>SetFormulaPredicate P\<close> by simp
  show ?thesis
    unfolding  abstract_foundation_iff[of "\<lambda> x. \<forall> y. y \<epsilon> x \<longrightarrow> \<not> P (\<Xi>(0:=y))" "\<lambda> x. \<not> P (\<Xi>(0:=x))", unfolded not_not]
    using  epsind[OF SP, rule_format, of \<Xi>] \<open>\<exists> x. P (\<Xi> (0:=x))\<close>
    by blast+
qed

sublocale L_regsch
  using epsind_regsch by unfold_locales blast

end 

subsection Separation

locale L_sep = set_signature + 
  assumes sep: "SetFormulaPredicate P \<Longrightarrow> \<forall>x. \<exists> z. \<forall> u. (u \<epsilon> z \<longleftrightarrow>  u \<epsilon> x \<and> P (\<Xi>(0:= u)))" 

begin

lemma sep_n: assumes "SetFormulaPredicate P" shows "\<forall>x. \<exists> z. \<forall> u. (u \<epsilon> z \<longleftrightarrow>  u \<epsilon> x \<and> P (\<Xi>(n:= u)))"
  using sep[OF swap_variables, OF assms, of "\<Xi>(n:= \<Xi> 0)" n 0]
  by (cases "n = 0", simp) (simp del: neq0_conv add: fun_upd_twist[of n 0])

lemma sep_sp: assumes "SetProperty P" shows "\<forall>x. \<exists> z. \<forall> u. (u \<epsilon> z \<longleftrightarrow>  u \<epsilon> x \<and> P u)" 
  using sep[OF assms[unfolded SetProperty_def]] by simp

lemma sep_sr: assumes "SetRelation P" shows "\<forall>x. \<exists> z. \<forall> u. (u \<epsilon> z \<longleftrightarrow>  u \<epsilon> x \<and> P u r)" 
  using sep[OF assms[unfolded SetRelation_def]] by simp

sublocale L_empty
  by unfold_locales (use sep[OF SFP_const[of False]] in force) 

end

locale L_setext_sep = L_setext + L_sep

begin

thm sep

lemma separ_def_sfp: assumes "SetFormulaPredicate P"
  shows "u \<epsilon> separationM y (\<lambda> x. P(\<Xi>(n:=x))) \<longleftrightarrow> (u \<epsilon> y \<and> (P (\<Xi>(n:= u))))"
  using  collect_def_ex[OF sep_n[rule_format], OF assms] separationM_def by simp

lemma separ_def_sp: assumes "SetProperty P"
  shows "u \<epsilon> separationM y (\<lambda> x. P x) \<longleftrightarrow> (u \<epsilon> y \<and> P u)"
  using separ_def_sfp[OF assms[unfolded SetProperty_def], of _ _ _ 0] by simp

lemma separ_def_sr: assumes "SetRelation P"
  shows "u \<epsilon> separationM y (\<lambda> x. P x r) \<longleftrightarrow> (u \<epsilon> y \<and> P u r)"
  using separ_def_sfp[OF assms[unfolded SetRelation_def], of _ _ _ 0] by simp

lemma least_def':
  assumes "Q (\<Xi>(n:=w))" and "SetFormulaPredicate Q"
  shows "u \<epsilon> \<Inter>\<^sub>M (\<lambda> x. Q (\<Xi>(n:=x))) \<longleftrightarrow> (\<forall> y. Q (\<Xi>(n:=y)) \<longrightarrow> u \<epsilon> y)"
proof-
  from bounded_free[OF assms(2)]
  obtain m where m: "Q \<Xi> = Q \<Xi>'" if "\<forall>i. i < m \<longrightarrow> \<Xi> i = \<Xi>' i" for \<Xi> \<Xi>'
    by blast
  have k: "Q (\<Xi>(m+n+1 := x, n := y)) \<longleftrightarrow> Q (\<Xi>(n := y))" for x y
    by (rule m) force+
  have aux: "(\<Xi>(n := a)) n = a" for \<Xi> and a::'a
    by simp
  have sfp: "SetFormulaPredicate (\<lambda> \<Xi>. (\<forall> y. Q (\<Xi>(n:=y)) \<longrightarrow> ((\<Xi>(n:=y)) (m+n+1)) \<epsilon> y))"
    by (rule SFP_all[of "\<lambda> \<Xi>.  Q (\<Xi>) \<longrightarrow> (\<Xi>) (m+n+1) \<epsilon> (\<Xi> n)", of n, unfolded aux], unfold logsimps) (rule | fact)+
  have iff: "(v \<epsilon> w \<and> (\<forall>y. Q (\<Xi>(n := y)) \<longrightarrow> v \<epsilon> y)) \<longleftrightarrow> (\<forall>y. Q (\<Xi>(n := y)) \<longrightarrow> v \<epsilon> y)" for v
    using assms(1) by blast
  have sep: "(v \<epsilon> separationM w (\<lambda>x. \<forall>y. Q (\<Xi>(n := y)) \<longrightarrow> x \<epsilon> y)) = (\<forall>y. Q (\<Xi>(n := y)) \<longrightarrow> v \<epsilon> y)" for v
    using separ_def_sfp[of _  v, OF sfp, of w \<Xi> "m+n+1"] iff[of v] 
     unfolding k by force 
  show ?thesis
    unfolding leastM_def using collect_def'
    using collect_def'[of "separationM w (\<lambda>x. \<forall>y. Q (\<Xi>(0 := y)) \<longrightarrow> u \<epsilon> y)"] sep by force
qed

lemma least_def_ex:
   "\<exists> w. Q (\<Xi>(n := w)) \<Longrightarrow> SetFormulaPredicate Q \<Longrightarrow> 
   u \<epsilon> \<Inter>\<^sub>M (\<lambda> x. Q (\<Xi>(n:=x))) \<longleftrightarrow> (\<forall> y. Q (\<Xi>(n:=y)) \<longrightarrow> u \<epsilon> y)"
  using least_def' by force

lemma intersection_def'[set_defs]: "z \<epsilon> x \<inter>\<^sub>M y \<longleftrightarrow> z \<epsilon> x \<and> z \<epsilon> y"
  using separ_def_sfp[of "\<lambda> \<Xi>. \<Xi>(0) \<epsilon> \<Xi>(1)" z x, rule_format, of "undefined(1:=y)" 0, simplified] 
  unfolding intersectionM_def separationM_def.

lemma intersect_subset: "x \<inter>\<^sub>M y \<subseteq>\<^sub>M x" "x \<inter>\<^sub>M y \<subseteq>\<^sub>M y"
  unfolding set_defs by simp_all 

end

subsection \<open>Transitive closure\<close>

locale L_ts = set_signature +
  assumes ts: "\<forall> x. \<exists> z. (transM z \<and> (x \<subseteq>\<^sub>M z))" 

locale L_setext_sep_ts = L_setext + L_sep + L_ts

begin

sublocale L_setext_sep
  by unfold_locales

lemma leastTS_def' : "u \<epsilon> leastTS x \<longleftrightarrow> (\<forall> v. transM v \<and> x \<subseteq>\<^sub>M v \<longrightarrow> u \<epsilon> v)" 
   (is "u \<epsilon> leastTS x \<longleftrightarrow> (\<forall> v. ?Q v \<longrightarrow> u \<epsilon> v)")
  by (rule least_def_ex[of "\<lambda> \<Xi>. transM (\<Xi> 0) \<and> \<Xi> 1 \<subseteq>\<^sub>M \<Xi> 0" "undefined(1:=x)" 0, 
  simplified, OF ts[rule_format], folded leastTS_def])
  (unfold logsimps set_defs, rule+)

lemma leastTS_is_transitive: "transM (leastTS x)"
  using leastTS_def' unfolding transM_def subsetM_def by blast

end

locale L_setext_sep_reg = L_setext + L_sep + L_reg

locale L_setext_sep_reg_ts = L_setext + L_sep + L_reg + L_ts

begin

sublocale L_empty
  by (simp add: L_empty_axioms)

sublocale L_setext_sep_ts
  by unfold_locales

sublocale L_regsch
proof (unfold_locales, rule)
  fix P \<Xi>
  assume "SetFormulaPredicate P"
  assume "\<exists> x. P (\<Xi>(0:=x))"
  then obtain x where "P (\<Xi>(0:=x))" 
    by blast
  have "x \<subseteq>\<^sub>M (leastTS x)"  
    using leastTS_def' subsetM_def by blast
  define w where "w = separationM (leastTS x) (\<lambda> x. P (\<Xi>(0:=x)))"
  then have w: "u \<epsilon> w \<longleftrightarrow> u \<epsilon> leastTS x \<and> P (\<Xi>(0:=u))" for u 
    using separ_def_sfp[OF \<open>SetFormulaPredicate P\<close>] by blast
  show "\<exists>x. P (\<Xi>(0 := x)) \<and> (\<forall>y. y \<epsilon> x \<longrightarrow> \<not> P (\<Xi>(0 := y)))"
  proof(cases)
    assume "\<exists> v. v \<epsilon> w"
    have "(\<exists> v. v \<epsilon> w)\<longrightarrow>(\<exists> v. (v \<epsilon> w \<and> ( \<forall> t. (t \<epsilon> v  \<longrightarrow> \<not> t \<epsilon> w ) ) ) )" 
      using reg by blast    
    then have "(\<exists> v. (v \<epsilon> w \<and> ( \<forall> t. (t \<epsilon> v  \<longrightarrow> \<not> t \<epsilon> w ) ) ) )" using \<open>\<exists> v. v \<epsilon> w\<close> by blast
    then obtain v where "v \<epsilon> w" and v: "t \<epsilon> v  \<longrightarrow> \<not> t \<epsilon> w" for t by blast  
    have "P (\<Xi>(0 := v))" 
      using w \<open>v \<epsilon> w\<close> by blast
    have "v \<epsilon> leastTS x" 
      using w \<open>v \<epsilon> w\<close> by blast
    have "v \<subseteq>\<^sub>M leastTS x"
      using leastTS_is_transitive \<open>v \<epsilon> leastTS x\<close> transM_def by blast
    have "t \<epsilon> v \<longrightarrow> \<not> P (\<Xi>(0 := t))" for t 
      using \<open>v \<subseteq>\<^sub>M leastTS x\<close> w v unfolding subsetM_def by blast 
    then have "\<forall> t. (t \<epsilon> v \<longrightarrow> \<not> P (\<Xi>(0 := t)))" by blast
    then have "\<exists>x. P (\<Xi>(0 := x))\<and> (\<forall>y. y \<epsilon> x \<longrightarrow> \<not> P (\<Xi>(0 := y)))"
      using \<open>P (\<Xi>(0 := v))\<close> by blast
    then show ?thesis by blast
  next
    assume  "\<not> (\<exists> v. v \<epsilon> w)"
    then have "\<forall> v. (v \<epsilon> leastTS x \<longrightarrow> \<not> P (\<Xi>(0 := v)) )" 
      using w  by blast
    then have  "\<forall> v. (v \<epsilon> x \<longrightarrow> \<not> P (\<Xi>(0 := v)) )" 
       using subsetM_def \<open>x \<subseteq>\<^sub>M leastTS x\<close> by blast
    then show ?thesis using \<open>P (\<Xi>(0 := x))\<close> by blast 
  qed
qed

end

subsection Replacement

locale L_repl = set_signature + 
  assumes replf:  "SetFormulaPredicate P \<Longrightarrow> (\<forall> u. \<exists>! v. P (\<Xi>(0:=u, 1:= v))) \<longrightarrow> (\<forall> x. \<exists> z. \<forall> v. v \<epsilon> z \<longleftrightarrow> (\<exists> u. u \<epsilon> x \<and> P (\<Xi>(0:=u, 1:= v))))"

locale L_setext_empty_repl = L_setext + L_empty + L_repl

begin

sublocale L_setext_empty
  by unfold_locales

text \<open>We show that replacing by full functions is equivalent to
 replacing by partial functions.\<close>

lemma replp: assumes "SetFormulaPredicate P" and func: "\<forall> u v w. P (\<Xi>(0:=u, 1:= v)) \<and> P (\<Xi>(0:=u, 1:= w)) \<longrightarrow> v = w"
  shows "\<forall> x. \<exists> z. (\<forall> v. v \<epsilon> z \<longleftrightarrow> (\<exists> u. u \<epsilon> x \<and> P (\<Xi>(0:=u, 1:= v))))"
proof
  fix x
  show "\<exists>z. \<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> x \<and> P (\<Xi>(0:=u, 1:= v)))"
  proof (cases "\<exists> u v. u \<epsilon> x \<and> P (\<Xi>(0:=u, 1:= v))")
    assume "\<nexists>u v. u \<epsilon> x \<and> P (\<Xi>(0:=u, 1:= v))"
    then show "\<exists>z. \<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> x \<and> P (\<Xi>(0:=u, 1:= v)))"
      using exI[of "\<lambda> z. \<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> x \<and> P (\<Xi>(0:=u, 1:= v)))" \<emptyset>] empty by blast 
  next    
    assume ex: "\<exists> u v. u \<epsilon> x \<and> P (\<Xi>(0:=u, 1:= v))"
    then obtain v where ex: "\<exists>u. u \<epsilon> x \<and> P (\<Xi>(0:=u, 1:= v))"  
      by blast
    from bounded_free[OF assms(1)]
    obtain k where k0: "\<forall>\<Xi> \<Xi>'. (\<forall>i<k. \<Xi> i = \<Xi>' i) \<longrightarrow> P \<Xi> = P \<Xi>'"
      by blast
    let ?k = "Suc (max k 1)"
    have k: "P(\<Xi>) \<longleftrightarrow> P(\<Xi>(?k:= a))" "1 < ?k" for \<Xi> a
      by (rule k0[rule_format, of \<Xi> "\<Xi>(?k:= a)"], force) simp   
    have twist: "\<Xi>(Suc (max k 1) := a, 0 := b, 1 := c) = \<Xi>(0 := b, 1 := c, Suc (max k 1) := a)" for a b c
      by auto
    have canc: "P(\<Xi>(?k:=a,0:=b,1:=c)) = P(\<Xi>(0:=b,1:=c))" "\<Xi>(?k:=a,0:=b,1:=c,1:=d) = \<Xi>(?k:=a,0:=b,1:=d)"
     "(\<Xi>(?k := a, 0 := b, 1 := c)) 1 = c" "(\<Xi>(?k := a, 0 := b, 1 := c)) ?k = a" for a b c d
      unfolding twist using k(1) by auto
    define Q :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool" where 
    "Q = (\<lambda> \<Xi>. (if \<exists> c. P (\<Xi>(1:= c)) then P \<Xi>  else \<Xi> 1 = \<Xi> ?k))"
    have "\<exists>! v'. Q (\<Xi>(?k:=v,0:=u,1:=v'))" for u
      unfolding Q_def canc using ex func by metis
    hence ex1: "\<forall> u. \<exists>! w. Q (\<Xi>(?k:=v,0:=u,1:=w))"
      by simp 
    have "SetFormulaPredicate Q"
      unfolding Q_def by (simp, unfold logsimps) (rule | fact)+
    from replf[rule_format, OF this ex1[rule_format], of x] 
    have  Qset: "\<exists>z. \<forall>w. (w \<epsilon> z) = (\<exists>u. u \<epsilon> x \<and> Q(\<Xi>(?k:=v,0:=u,1:=w)))".
    have P_iff_Q: "(\<exists>u. u \<epsilon> x \<and> P (\<Xi>(0 := u, 1 := w))) \<longleftrightarrow> (\<exists>u. u \<epsilon> x \<and> Q (\<Xi>(?k:=v, 0 := u, 1 := w)))" for w
      unfolding Q_def canc  using ex by auto 
    show ?thesis
      using Qset unfolding P_iff_Q.
  qed
qed

lemma replp_vars: assumes "SetFormulaPredicate P" and func: "\<forall> u v w. P (\<Xi>(k:=u, l:= v)) \<and> P (\<Xi>(k:=u, l:= w)) \<longrightarrow> v = w"
  shows "\<forall> x. \<exists> z. (\<forall> v. v \<epsilon> z \<longleftrightarrow> (\<exists> u. u \<epsilon> x \<and> P (\<Xi>(k:=u, l:= v))))"
proof-
  from bounded_free[OF \<open>SetFormulaPredicate P\<close>]
  obtain m where m: "P \<Xi> = P \<Xi>'" if "\<forall>i<m. \<Xi> i = \<Xi>' i" for \<Xi> \<Xi>'
    by blast
  let ?m = "Suc (k + l + m)"  
  let ?f = "id(0 := ?m, 1 := Suc ?m, k:= 0,l := 1)"
  let ?Q = "\<lambda> X. (P (\<lambda> b. X (?f  b)))"
  let ?X = "\<Xi>(?m:= \<Xi> 0,(Suc ?m):= \<Xi> 1)" 
  have sfpq:  "SetFormulaPredicate ?Q"
    using transform_variables[OF \<open>SetFormulaPredicate P\<close>] by simp
  have small: "\<forall> i < m. (\<Xi>(k := u, l := v)) i = (?X (0 := u, 1 := v)) (?f i)" for u v
    by auto
  have equiv: "(P (\<Xi>(k := u, l := v))) \<longleftrightarrow> (?Q (?X (0 := u, 1 := v)))" for u v
    by (rule m[of "\<Xi>(k := u, l := v)" "\<lambda> b. (?X (0 := u, 1 := v))(?f b)"]) fact
  then have funcq: "(\<forall>u v w. ?Q (?X(0 := u, 1 := v)) \<and> ?Q (?X(0 := u, 1 := w)) \<longrightarrow> v = w)"
    using func by blast 
  show ?thesis
    using replp[OF sfpq funcq] unfolding equiv.    
qed

lemma replp_SR: assumes "SetRelation P" "\<forall> u v w. P u v \<and> P u w \<longrightarrow> v = w"
  shows "\<forall> x. \<exists> z. (\<forall> v. v \<epsilon> z \<longleftrightarrow> (\<exists> u. u \<epsilon> x \<and> P u v))"
  using assms unfolding SetRelation_def using replp[of "\<lambda>\<Xi>. P (\<Xi> 0) (\<Xi> 1)"] by fastforce    

lemma replace_def':  
  assumes "SetFormulaPredicate P" "\<forall> u v w. P(\<Xi>(k:=u, l:= v)) \<and> P(\<Xi>(k:=u, l:= w)) \<longrightarrow> v = w"
  shows "\<forall> v. v \<epsilon> replaceM (\<lambda> u v. P(\<Xi>(k:=u, l:= v))) x \<longleftrightarrow> (\<exists> u. u \<epsilon> x \<and> (P(\<Xi>(k:=u, l:= v))))"
  using collect_def_ex[of  "\<lambda> v. (\<exists>u. u \<epsilon> x \<and> P(\<Xi>(k:=u, l:= v)))", OF replp_vars[OF assms, rule_format], folded replaceM_def] by blast

sublocale L_setext_sep
proof (unfold_locales, rule)
  fix P \<Xi> x
  assume sfp: "SetFormulaPredicate P"
  have t: "(\<lambda>n. if n = 0 then v else ((\<lambda>i. \<Xi> (i - 1))(0 := v)) (n+1)) = \<Xi>(0 := v)" for v and \<Xi> :: "nat \<Rightarrow> 'a" 
    by auto
  have "SetFormulaPredicate (\<lambda> \<Xi>. (\<Xi> 0) = (\<Xi> 1) \<and> P (\<lambda> n. \<Xi> (n+1)))"
    unfolding logsimps by rule+ (rule transform_variables[OF sfp])
  from replp[rule_format, OF this, of "\<lambda> i. \<Xi> (i - 1)" x]
  show "\<exists>z. \<forall>u. (u \<epsilon> z) = (u \<epsilon> x \<and> P (\<Xi>(0 := u)))"
    by (simp del: One_nat_def add: t)  
qed

end

subsection \<open>Set pair\<close>

locale L_pair = set_signature + 
  assumes pair: "\<forall> x y. \<exists> z. \<forall> v. v \<epsilon> z \<longleftrightarrow> v = x \<or> v = y"

locale L_setext_pair = L_setext + L_pair

begin

lemma singletonM_ex: "\<exists> x. \<forall> u. u \<epsilon> x \<longleftrightarrow>  u = y" 
  using pair by meson

lemma singleton_def'[set_defs]: "u \<epsilon> {y}\<^sub>M \<longleftrightarrow>  u = y"
  using collect_def_ex[OF singletonM_ex[rule_format], folded singletonM_def]. 

lemma singleton_eq[set_defs]: "u = {y}\<^sub>M \<longleftrightarrow>  (\<forall> v. v \<epsilon> u \<longleftrightarrow> v = y)"
  unfolding setext  set_defs by blast

lemma pair_def'[set_defs]: "u \<epsilon> {x,y}\<^sub>M \<longleftrightarrow> u = x \<or> u = y"
  using collect_def_ex[OF pair[rule_format], folded pairM_def].

lemma pair_eq [set_defs]: "w = {x,y}\<^sub>M \<longleftrightarrow> (\<forall> u. (u \<epsilon> w) \<longleftrightarrow>  u = x \<or> u = y)"
  unfolding setext[of w] set_defs by simp 

end

subsection \<open>Set successor\<close>

locale L_setsuc = set_signature + 
  assumes setsuc: "\<forall> x y. \<exists> z. \<forall> u. u \<epsilon> z \<longleftrightarrow> u \<epsilon> x \<or> u = y"

subsection Powerset

locale L_power = set_signature +
  assumes 
          power: "\<forall> x. \<exists> y. (\<forall> u. u \<epsilon> y \<longleftrightarrow> u \<subseteq>\<^sub>M x)"

locale L_setext_empty_power = L_setext + L_empty + L_power

begin

sublocale L_setext_empty
  by unfold_locales

lemma powerset_def'[set_defs]: "u \<epsilon> (\<PP> x) \<longleftrightarrow> u \<subseteq>\<^sub>M x"
  using collect_def_ex[OF power[rule_format], folded powersetM_def].

lemma "\<emptyset> \<epsilon> \<PP> \<emptyset>"
  using empty_is_subset powerset_def' by blast

lemma set_one_mem [simp]: "u \<epsilon> \<PP> \<emptyset> \<longleftrightarrow> u = \<emptyset>"
  unfolding powerset_def' subsetM_def empty_set_def' by force 

lemma set_one_def: "\<PP> \<emptyset> = {\<emptyset>}\<^sub>M"
  unfolding singletonM_def using collect_def'[of "\<PP> \<emptyset>"] unfolding set_one_mem by force 

lemma set_two_mem: "u \<epsilon> \<PP> (\<PP> \<emptyset>) \<longleftrightarrow> u = \<emptyset> \<or> u = {\<emptyset>}\<^sub>M"
  unfolding powerset_def' set_one_def 
proof
  show "u = \<emptyset> \<or> u = {\<emptyset>}\<^sub>M" if "u \<subseteq>\<^sub>M {\<emptyset>}\<^sub>M" 
    using  that[unfolded subsetM_def] empty_set_def'
    unfolding setext[of _ "{\<emptyset>}\<^sub>M"]  set_one_mem[unfolded set_one_def] by blast 
  show "u = \<emptyset> \<or> u = {\<emptyset>}\<^sub>M \<Longrightarrow> u \<subseteq>\<^sub>M {\<emptyset>}\<^sub>M"
    using empty_is_subset subsetM_refl by blast
qed

end

locale L_setext_empty_power_repl = L_setext + L_empty + L_power + L_repl

begin

sublocale L_setext_empty
  by unfold_locales

sublocale L_setext_empty_repl
  by unfold_locales

sublocale L_setext_empty_power
  by unfold_locales

sublocale L_pair
proof (unfold_locales, rule, rule)
  fix x y :: 'a
  let ?P = "(\<lambda>\<Xi>. \<Xi> 0 = \<emptyset> \<and> \<Xi> 1 = \<Xi> 2 \<or> \<Xi> 0 = {\<emptyset>}\<^sub>M \<and> \<Xi> 1 = \<Xi> 3)"
  let ?\<Xi> = "undefined(2::nat := x, 3 := y)"
  have singletonM_ex: "\<exists> x. \<forall> u. u \<epsilon> x \<longleftrightarrow>  u = y" for y
  proof-
    have sfp: "SetFormulaPredicate (\<lambda> \<Xi>. \<Xi> 0 = \<emptyset> \<and> \<Xi> 1 = \<Xi> 2)" 
      unfolding logsimps set_defs by rule+
    show ?thesis
      using replp[OF sfp, rule_format, of _  "\<PP> \<emptyset>"] by simp
  qed
  have sing_def: "(u = {v}\<^sub>M) \<longleftrightarrow> (\<forall> a. a \<epsilon> u \<longleftrightarrow> a = v)" for u v
    using collect_def_ex[OF singletonM_ex[rule_format], folded singletonM_def]
    unfolding setext by simp
  have sfp: "SetFormulaPredicate ?P"
    unfolding logsimps set_defs sing_def by rule+
  have "\<emptyset> \<noteq> {\<emptyset>}\<^sub>M"
    using set_one_def set_two_mem by fastforce
  hence Pfun: "\<forall>u v w. ?P (?\<Xi>(0 := u, 1 := v)) \<and> ?P (?\<Xi>(0 := u, 1 := w)) \<longrightarrow> v = w"
    by force 
  from replp[OF sfp Pfun, rule_format, of "\<PP> (\<PP> (\<emptyset>))", unfolded set_two_mem]
  show "\<exists> z. \<forall> v. v \<epsilon> z \<longleftrightarrow> v = x \<or> v = y"
    by auto
qed

sublocale L_setext_pair
  by unfold_locales

lemma [set_defs]: "(u = {v}\<^sub>M) \<longleftrightarrow> (\<forall> a. a \<epsilon> u \<longleftrightarrow> a = v)"
  unfolding setext singleton_def' by argo

lemma SFP_singleton [simp]: "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> n = {\<emptyset>}\<^sub>M)"
  unfolding setext set_defs logsimps by rule+ 

sublocale L_setsuc
proof (unfold_locales, rule, rule)
  fix x y 
  let ?P = "(\<lambda> \<Xi>. \<Xi> 0 \<subseteq>\<^sub>M \<Xi> 2 \<and> (\<Xi> 1 \<epsilon> \<Xi> 2 \<and> (\<forall> q. q \<epsilon> \<Xi> 0 \<longleftrightarrow> q = \<Xi> 1) \<or> (\<Xi> 1 = \<Xi> 3 \<and> \<not>(\<exists> z. \<forall> q. q \<epsilon> \<Xi> 0 \<longleftrightarrow> q = z))))"
  have sfp: "SetFormulaPredicate ?P"
    unfolding logsimps set_defs by rule+
  have "\<exists>z. \<forall>v. (v \<epsilon> z) =
          (\<exists>u. u \<epsilon> \<PP> x \<and>
               u \<subseteq>\<^sub>M (undefined((2::nat) := x, 3 := y)) 2 \<and>
               (v \<epsilon> (undefined((2::nat) := x, 3 := y)) 2 \<and> (\<forall>q. (q \<epsilon> u) = (q = v)) \<or>
                v = (undefined((2::nat) := x, 3 := y)) 3 \<and> (\<forall>z. \<exists>q. (q \<epsilon> u) = (q \<noteq> z))))"
    by (rule replp[OF sfp, simplified, rule_format, of "undefined ((2:: nat):=x, 3:=y)" "\<PP> x"]) blast
  then obtain s where s: "\<forall>v. (v \<epsilon> s) =
  (\<exists>u. u \<epsilon> \<PP> x \<and> u \<subseteq>\<^sub>M x \<and> (v \<epsilon> x \<and> (\<forall>q. (q \<epsilon> u) = (q = v)) \<or> v = y \<and> (\<nexists>z. \<forall>q. (q \<epsilon> u) = (q = z))))"
    by auto
  have "v \<epsilon> s \<longleftrightarrow> (v \<epsilon> x \<or> v = y)" for v
  proof
    show "v \<epsilon> s \<Longrightarrow> v \<epsilon> x \<or> v = y"
      unfolding s[rule_format] by blast
    show "v \<epsilon> x \<or> v = y \<Longrightarrow> v \<epsilon> s"
    proof (erule disjE)
      assume "v \<epsilon> x"
      hence "{v}\<^sub>M \<epsilon> \<PP> x \<and> {v}\<^sub>M \<subseteq>\<^sub>M x \<and> (v \<epsilon> x \<and> (\<forall>q. (q \<epsilon> {v}\<^sub>M) = (q = v)))"
        unfolding set_defs by blast
      then show "v \<epsilon> s"
        unfolding s[rule_format] by blast
    next
      assume "v = y"
      hence "\<emptyset> \<epsilon> \<PP> x \<and> \<emptyset> \<subseteq>\<^sub>M x \<and> (v = y \<and> (\<nexists>z. \<forall>q. (q \<epsilon> \<emptyset>) = (q = z)))"  
        unfolding set_defs by force
      then show "v \<epsilon> s"
        unfolding s[rule_format] by blast
    qed
  qed
  then show "\<exists>z. \<forall>u. (u \<epsilon> z) = (u \<epsilon> x \<or> u = y)"
    by blast
qed

end

subsection \<open>Union\<close>

locale L_union = set_signature + 
  assumes union: "\<forall> x. \<exists> y.\<forall> v. v \<epsilon> y \<longleftrightarrow> (\<exists> u. u \<epsilon> x \<and> v \<epsilon> u)"

locale L_setext_union = L_setext + L_union 

begin

lemma union_def'[set_defs]: "u \<epsilon> \<Union>\<^sub>M x \<longleftrightarrow> (\<exists> v. v \<epsilon> x \<and> u \<epsilon> v)"
  using collect_def_ex[OF union[rule_format, of x], folded unionM_def[of x]].

lemma union_trans_trans: assumes "\<forall> v. v \<epsilon> x \<longrightarrow> transM v"
  shows "transM (\<Union>\<^sub>M x)"
  using assms unfolding transM_def union_def' subsetM_def by blast

end

locale L_setext_pair_union = L_setext + L_pair + L_union 

begin

sublocale L_setext_pair
  by unfold_locales

sublocale L_setext_union
  by unfold_locales

lemma binunion_def'[set_defs]: "u \<epsilon> x \<union>\<^sub>M y \<longleftrightarrow> u \<epsilon> x \<or> u \<epsilon> y"
  unfolding binunionM_def
  using collect_def_ex[OF union[rule_format, of "{x,y}\<^sub>M", unfolded pair_def'], of u]
  by force

lemma union_of_suc_of_trans: assumes "transM y" shows "\<Union>\<^sub>M (y \<union>\<^sub>M {y}\<^sub>M) = y"
  using assms unfolding setext[of _ y] set_defs by blast  

lemma set_suc: " \<exists> z. \<forall> u. (u \<epsilon> z \<longleftrightarrow> u \<epsilon> x \<or> u = y) "
proof-
  let ?z = " x \<union>\<^sub>M {y}\<^sub>M" 
  have "u \<epsilon> ?z \<longleftrightarrow> (u \<epsilon> x \<or> u = y)" for u 
    unfolding binunion_def' singleton_def' by blast
  then show ?thesis by blast
qed

sublocale  L_setsuc 
  using set_suc by unfold_locales blast

lemma ord_pred_inj: assumes "ordM x" "ordM y" "x \<union>\<^sub>M {x}\<^sub>M = y \<union>\<^sub>M {y}\<^sub>M" 
  shows "x = y"
  using assms unfolding setext[of x] setext[of "x \<union>\<^sub>M {x}\<^sub>M"] set_defs by metis

lemma SFP_suc_mem[simp, intro]: "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> k \<epsilon> \<Xi> l \<union>\<^sub>M {\<Xi> m}\<^sub>M)"
  unfolding set_defs by rule+ 

lemma SFP_suc_eq[simp, intro]: "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> k = \<Xi> l \<union>\<^sub>M {\<Xi> m}\<^sub>M)"
  unfolding set_defs setext logsimps by rule+ 

lemma SFP_sing_suc_eq [simp, intro]:  "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> k = {\<Xi> l \<union>\<^sub>M {\<Xi> m}\<^sub>M}\<^sub>M)"
  unfolding singleton_eq unfolding logsimps by rule+

lemma SFP_mem_ordered_pair[simp, intro]: "SetFormulaPredicate (\<lambda> \<Xi>. \<Xi> k \<epsilon> \<langle>\<Xi> l, \<Xi> m\<rangle>)"
  unfolding set_defs logsimps ordered_pairM_def by rule+

lemma SFP_eq_ordered_pair [simp, intro]: "SetFormulaPredicate (\<lambda> \<Xi>. \<Xi> k = \<langle>\<Xi> l,\<Xi> m\<rangle>)"
  unfolding setext logsimps by rule+

lemma SFP_ordered_pair_mem[simp,intro]: "SetFormulaPredicate (\<lambda>\<Xi>. \<langle>\<Xi> k,\<Xi> l\<rangle> \<epsilon> \<Xi> m)"
proof-
  have "SetFormulaPredicate (\<lambda>\<Xi>. \<exists> u. u = \<langle>\<Xi> k,\<Xi> l\<rangle> \<and> u \<epsilon> \<Xi> m)"
    unfolding setext logsimps by rule+
  thus ?thesis
    by simp
qed   

lemma SFP_ordered_pair_suc_mem[simp,intro]: "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> k \<epsilon> \<langle>\<Xi> l,\<Xi> m \<union>\<^sub>M {\<Xi> n}\<^sub>M\<rangle>)"
  unfolding ordered_pairM_def set_defs logsimps by rule+

\<comment>\<open>An explicit proof avoiding too many quantifiers.\<close>
lemma SFP_ordered_pair_suc_eq[simp,intro]: "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> k = \<langle>\<Xi> l,\<Xi> m \<union>\<^sub>M {\<Xi> n}\<^sub>M\<rangle>)"
proof-
  let ?Q = "\<lambda> \<Xi>. \<Xi> (m+n+l+k+1) = \<Xi> m \<union>\<^sub>M {\<Xi> n}\<^sub>M \<and> \<Xi> k = \<langle>\<Xi> l,\<Xi> (m+n+l+k+1)\<rangle>"
  show ?thesis
    by (rule SFP_ex[of ?Q "m+n+l+k+1", simplified]) (unfold logsimps, rule+)
qed

end

locale L_setext_empty_union_repl_pair = L_setext + L_empty + L_union + L_repl + L_pair

locale L_setext_empty_union_repl_pair_regsch = L_setext + L_empty + L_union + L_repl + L_pair +  L_regsch

begin

sublocale L_setext_empty_repl
  by unfold_locales

sublocale L_setext_union
  by unfold_locales

sublocale L_setext_pair_union
  by unfold_locales

thm leastTS_def[unfolded leastM_def]  

lemma transitive_closure_ex:
  shows "\<forall> x. \<exists> z. x \<subseteq>\<^sub>M z \<and> transM z \<and> (\<forall> u. u \<epsilon> z \<longleftrightarrow> (\<forall> t. x \<subseteq>\<^sub>M t \<and> transM t \<longrightarrow> u \<epsilon> t))"
    (is "\<forall> x. \<exists> z. ?TC x z" is "\<forall> x. ?hasTC x") 
proof
  fix x' :: 'a
  have ind_rule: "SetFormulaPredicate (\<lambda>\<Xi>. ?hasTC(\<Xi> 0)) \<Longrightarrow> (\<And>x. (\<And>y. y \<epsilon> x \<Longrightarrow> ?hasTC y) \<Longrightarrow> ?hasTC x) \<Longrightarrow> ?hasTC x'"
    using  regsch_epsind[rule_format, of "\<lambda> \<Xi>. ?hasTC(\<Xi> 0)" "undefined" x', unfolded fun_upd_same] by argo
  show "\<exists>z. x' \<subseteq>\<^sub>M z \<and> transM z \<and> (\<forall>u. (u \<epsilon> z) = (\<forall>t. x' \<subseteq>\<^sub>M t \<and> transM t \<longrightarrow> u \<epsilon> t))"
  proof (rule ind_rule)
    fix x
    define TC where "TC = ?TC" \<comment> \<open>\<open>TC x z\<close> \<close>
    have sfp_tc: "SetFormulaPredicate (\<lambda>\<Xi>. TC (\<Xi> 0) (\<Xi> 1))"
      unfolding TC_def set_defs logsimps by rule+
    have tc_fun: "\<forall>u v w. TC u v \<and> TC u w \<longrightarrow> v = w"
      unfolding TC_def setext by blast
    show "SetFormulaPredicate (\<lambda>\<Xi>. ?hasTC(\<Xi> 0))"
      unfolding TC_def set_defs logsimps by rule+
    assume IP: "?hasTC y" if "y \<epsilon> x" for y
    define tcs where "tcs = \<Union>\<^sub>M (replaceM TC x)"
    have repl_x: "\<forall>v. (v \<epsilon> replaceM TC x) \<longleftrightarrow> (\<exists>u. u \<epsilon> x \<and> TC u v)" 
      by (rule replace_def'[OF sfp_tc, of _ 0 1 x, simplified fun_upd_same fun_upd_other]) fact   
    hence "transM tcs"
      unfolding TC_def tcs_def union_def' transM_def subsetM_def by blast
    hence tcs_mem: "w \<epsilon> tcs \<longleftrightarrow> (\<exists> y. y \<epsilon> x \<and> (\<exists> v. TC y v \<and> w \<epsilon> v))" for w
      unfolding tcs_def using union_def' repl_x by auto 
    show "?hasTC x"
    proof (rule exI[of _ "tcs \<union>\<^sub>M x"], fold conj_assoc, rule, rule)
      show "x \<subseteq>\<^sub>M tcs \<union>\<^sub>M x"
        unfolding tcs_def set_defs by blast
      show trans: "transM (tcs \<union>\<^sub>M x)"
        unfolding transM_def binunion_def'
      proof (rule, rule, erule disjE)
        show "y \<subseteq>\<^sub>M tcs \<union>\<^sub>M x" if "y \<epsilon> tcs" for y
          using \<open>transM tcs\<close> that unfolding transM_def binunion_def' subsetM_def by blast 
        show "y \<subseteq>\<^sub>M tcs \<union>\<^sub>M x" if "y \<epsilon> x" for y
          unfolding subsetM_def tcs_def binunion_def' union_def' repl_x[rule_format] 
        proof (rule, rule, rule disjI1)
          fix z
          assume "z \<epsilon> y" 
          obtain w where  "TC y w"
            unfolding TC_def using IP[OF \<open>y \<epsilon> x\<close>] by blast
          hence "z \<epsilon> w"
            using \<open>z \<epsilon> y\<close> unfolding TC_def subsetM_def by blast
          hence "(y \<epsilon> x \<and> TC y w) \<and> z \<epsilon> w"
            using \<open>y \<epsilon> x\<close> \<open>TC y w\<close> by blast
          then show "\<exists>v. (\<exists>u. u \<epsilon> x \<and> TC u v) \<and> z \<epsilon> v"
            by blast
        qed
      qed
      show "\<forall>u. (u \<epsilon> tcs \<union>\<^sub>M x) \<longleftrightarrow> (\<forall>t. x \<subseteq>\<^sub>M t \<and> transM t \<longrightarrow> u \<epsilon> t)"
      proof (rule, rule, rule, rule)
        \<comment> \<open> \<open>tcs \<union>\<^sub>M x\<close> is the least transitive superset\<close>
        fix u t
        assume "u \<epsilon> tcs \<union>\<^sub>M x" "x \<subseteq>\<^sub>M t \<and> transM t"
        consider "\<exists> y. y \<epsilon> x \<and> (\<exists> w. TC y w \<and> u \<epsilon> w)" | "u \<epsilon> x"
          using \<open>u \<epsilon> tcs \<union>\<^sub>M x\<close> unfolding set_defs tcs_def repl_x[rule_format] by blast
        then show "u \<epsilon> t"
        proof (cases)
          assume "\<exists> y. y \<epsilon> x \<and> (\<exists> w. TC y w \<and> u \<epsilon> w)"
          then obtain y w where y_w: "y \<epsilon> x" "TC y w" "u \<epsilon> w"
            by blast
          have "y \<subseteq>\<^sub>M t"
            using \<open>y \<epsilon> x\<close> \<open>x \<subseteq>\<^sub>M t \<and> transM t\<close> unfolding transM_def subsetM_def by blast
          then show "u \<epsilon> t"
            using \<open>x \<subseteq>\<^sub>M t \<and> transM t\<close> y_w unfolding TC_def by blast
        qed (use \<open>x \<subseteq>\<^sub>M t \<and> transM t\<close> subsetM_def in blast) \<comment> \<open>the trivial case \<open>u \<epsilon> x\<close>\<close>
      qed (use \<open>x \<subseteq>\<^sub>M tcs \<union>\<^sub>M x\<close> local.trans in blast)  \<comment> \<open>the trivial implication: \<open>tcs \<union>\<^sub>M x\<close> is a transitive  superset\<close>
    qed
  qed
qed

sublocale L_ts
    using transitive_closure_ex by unfold_locales blast   

end

locale L_setext_empty_power_union_repl  = L_setext + L_empty + L_power + L_union 
+ L_repl 
begin

sublocale L_setext_empty_power_repl
  by unfold_locales

sublocale L_setext_union
  by unfold_locales

lemma regular_not_self_mem: assumes "regular x" shows "\<not> x \<epsilon> x"
proof
  assume "x \<epsilon> x"
  with assms[unfolded regular_def, rule_format, of "{x}\<^sub>M"]
  show False
    unfolding subsetM_def  singleton_def' by blast
qed

sublocale L_setext_pair_union
  by unfold_locales

lemma regular_antisym_mem: assumes "regular x" "u \<epsilon> x" "v \<epsilon> x" shows "\<not> (u \<epsilon> v \<and> v \<epsilon> u)"
proof
  assume "u \<epsilon> v \<and> v \<epsilon> u"
  with \<open>regular x\<close>[unfolded regular_def, rule_format, of "{u,v}\<^sub>M"]
  show False
    unfolding set_defs  pair_def' using \<open>u \<epsilon> x\<close> \<open>v \<epsilon> x\<close> by blast 
qed

lemma regular_antisym2_mem: assumes "regular x" "u \<epsilon> x" "v \<epsilon> x" "w \<epsilon> x" shows "\<not> (u \<epsilon> v \<and> v \<epsilon> w \<and> w \<epsilon> u)"
proof
  assume "u \<epsilon> v \<and> v \<epsilon> w \<and> w \<epsilon> u"
  with \<open>regular x\<close>[unfolded regular_def, rule_format, of "{u,v}\<^sub>M \<union>\<^sub>M {w}\<^sub>M"]
  show False
    unfolding set_defs  pair_def' using \<open>u \<epsilon> x\<close> \<open>v \<epsilon> x\<close> \<open>w \<epsilon> x\<close>  regular_def by blast
qed

lemma binunion_emp[simp]: "\<emptyset> \<union>\<^sub>M t = t"
  unfolding setext binunion_def' by simp

lemma binunion_emp'[simp]: "t \<union>\<^sub>M \<emptyset> = t"
  unfolding setext binunion_def' by simp

lemma pow_setsuc_def'[simp]:  "u \<epsilon> x \<union>\<^sub>M {y}\<^sub>M \<longleftrightarrow> u \<epsilon> x \<or> u = y" 
  unfolding binunion_def' singleton_def'..

lemma triv_suc [simp]: "y \<epsilon> x \<Longrightarrow> x \<union>\<^sub>M {y}\<^sub>M = x"
  unfolding setext[of _ x] singleton_def' pow_setsuc_def' by blast 

lemma trans_suc: "transM x \<Longrightarrow> transM (x \<union>\<^sub>M {x}\<^sub>M)"
    unfolding transM_def pow_setsuc_def' subsetM_def by blast

lemma tarski_subset_tarski: assumes "tarski_fin x" "y \<subseteq>\<^sub>M x" shows "tarski_fin y"
  using assms unfolding tarski_fin_def set_defs by presburger

lemma tarski_suc_tarski: assumes "tarski_fin x" shows "tarski_fin (x \<union>\<^sub>M {y}\<^sub>M)"
  unfolding tarski_fin_def
proof (rule, rule, rule)
  \<comment> \<open>fix a system \<open>w\<close> for which we want to find the maximum\<close>
  fix w assume w: "\<forall>z. z \<epsilon> w \<longrightarrow> z \<subseteq>\<^sub>M x \<union>\<^sub>M {y}\<^sub>M" and "\<exists> z. z \<epsilon> w"
    \<comment> \<open>remove \<open>y\<close> from each element of \<open>w\<close>, call the result \<open>w'\<close>\<close>  
  let ?P = "\<lambda> \<Xi>. \<forall> a. a \<epsilon> \<Xi> 1 \<longleftrightarrow> a \<epsilon> \<Xi> 0 \<and> a \<noteq> \<Xi> 2"
  have sfp: "SetFormulaPredicate (\<lambda>\<Xi>. \<forall>v. (v \<epsilon> \<Xi> 1) = (v \<epsilon> \<Xi> 0 \<and> v \<noteq> \<Xi> 2))"
    unfolding logsimps by rule+
  have aux:  "(\<Xi>(2::nat := y, 0 := u, 1 := v)) 0 = u"
             "(\<Xi>(2 := y, 0 := u, 1 := v)) 1 = v"
             "(\<Xi>(2 := y, 0 := u, 1 := v)) 2 = y" for u v \<Xi>
    by simp_all
  have "\<exists> w'. \<forall> z. z \<epsilon> w' \<longleftrightarrow> (\<exists> u. u \<epsilon> w \<and> (\<forall> v. v \<epsilon> z \<longleftrightarrow> v \<epsilon> u \<and> v \<noteq> y))"
   by (rule replp[rule_format, of ?P "undefined(2:= y)" w, unfolded aux], fact)
    (unfold setext, simp)
  then obtain w' where w': "\<forall> z. z \<epsilon> w' \<longleftrightarrow> (\<exists> u. u \<epsilon> w \<and> (\<forall> v. v \<epsilon> z \<longleftrightarrow> v \<epsilon> u \<and> v \<noteq> y))"  
    by blast
   \<comment> \<open>get the maximum of \<open>w'\<close>\<close>
  obtain wmax' where wmax': "wmax' \<epsilon> w' \<and> (\<nexists>w. w \<epsilon> w' \<and> wmax' \<subset>\<^sub>M w)"
  proof (rule exE[OF assms[unfolded tarski_fin_def, rule_format, of w'], of thesis])   
    show "z \<subseteq>\<^sub>M x" if "z \<epsilon> w'" for z
      using \<open>z \<epsilon> w'\<close>[unfolded w'[rule_format, of z]] w unfolding subsetM_def by auto
    show "\<exists>x. x \<epsilon> w'"
    proof-
      obtain u where "u \<epsilon> w"
        using \<open>\<exists> z. z \<epsilon> w\<close> by blast 
      obtain u' where u': "\<forall> v. v \<epsilon> u' \<longleftrightarrow> v \<epsilon> u \<and> v \<noteq> y" 
      using sep[rule_format, of "\<lambda> \<Xi>. \<Xi> 0 \<noteq> \<Xi> 1" u "undefined(1:=y)"] by auto 
      show "\<exists>x. x \<epsilon> w'"
        unfolding w'[rule_format] using \<open>u \<epsilon> w\<close> u' by blast
    qed
  qed
  have "\<not> y \<epsilon> wmax'" "wmax' \<epsilon> w'" "\<nexists>w. w \<epsilon> w' \<and> wmax' \<subset>\<^sub>M w"
    using w' wmax' by blast+
  \<comment> \<open>Either \<open>wmax'\<close> or \<open>wmax' \<union>\<^sub>M {y}\<^sub>M\<close> is the desired maximum of \<open>w\<close>\<close>
  show "\<exists>z. z \<epsilon> w \<and> (\<nexists>v. v \<epsilon> w \<and> z \<subset>\<^sub>M v)"
  proof(cases) 
    assume "wmax' \<union>\<^sub>M {y}\<^sub>M \<epsilon> w"
    have "(\<nexists>v. v \<epsilon> w \<and> wmax' \<union>\<^sub>M {y}\<^sub>M \<subset>\<^sub>M v)"
    proof
      assume "\<exists>v. v \<epsilon> w \<and> wmax' \<union>\<^sub>M {y}\<^sub>M \<subset>\<^sub>M v"
      then obtain v where "v \<epsilon> w" and "wmax' \<union>\<^sub>M {y}\<^sub>M \<subset>\<^sub>M v"
        by blast
      obtain v' where v': "\<And> t. t \<epsilon> v' \<longleftrightarrow> t \<epsilon> v \<and> t \<noteq> y"
      using sep[rule_format, of "\<lambda> \<Xi>. \<Xi> 0 \<noteq> \<Xi> 1" v "undefined(1:=y)"] by auto 
      have "v' \<epsilon> w'"
        using \<open>v \<epsilon> w\<close> v' w' by auto
      have "wmax' \<subset>\<^sub>M v'"
        using \<open>wmax' \<union>\<^sub>M {y}\<^sub>M \<subset>\<^sub>M v\<close> \<open>\<not> y \<epsilon> wmax'\<close> unfolding set_defs setext[of wmax'] setext[of _ v] v' by blast 
      show False
        using wmax' \<open>v' \<epsilon> w'\<close> \<open>wmax' \<subset>\<^sub>M v'\<close> by blast
    qed 
    thus ?thesis
      using \<open>wmax' \<union>\<^sub>M {y}\<^sub>M \<epsilon> w\<close> by blast
  next
    assume "\<not> wmax' \<union>\<^sub>M {y}\<^sub>M \<epsilon> w" 
    hence "wmax' \<epsilon> w" 
    proof-
      obtain wmax where "wmax \<epsilon> w" and wmax: "\<forall> v. (v \<epsilon> wmax') = (v \<epsilon> wmax \<and> v \<noteq> y)"
        using \<open>wmax' \<epsilon> w'\<close>[unfolded w'[rule_format, of wmax']] \<open>\<not> y \<epsilon> wmax'\<close> by blast
      have "\<not> y \<epsilon> wmax"
      proof
        assume "y \<epsilon> wmax"
        hence "wmax = wmax' \<union>\<^sub>M {y}\<^sub>M"
          unfolding setext[of wmax] set_defs wmax[rule_format] by blast
        then show False
          using \<open>\<not> wmax' \<union>\<^sub>M {y}\<^sub>M \<epsilon> w\<close> \<open>wmax \<epsilon> w\<close> by blast 
      qed
      hence "wmax = wmax'"
        unfolding setext[of wmax] binunion_def' wmax[rule_format] by blast
      then show "wmax' \<epsilon> w"
        using \<open>wmax \<epsilon> w\<close> by blast
    qed
    have "(\<nexists>v. v \<epsilon> w \<and> wmax' \<subset>\<^sub>M v)"
    proof
      assume "\<exists>v. v \<epsilon> w \<and> wmax' \<subset>\<^sub>M v"
      then obtain v where "v \<epsilon> w" and "wmax' \<subseteq>\<^sub>M v" and "wmax' \<noteq> v"
        unfolding proper_subset_def' by blast
      obtain v' where v': "\<And> t. t \<epsilon> v' \<longleftrightarrow> t \<epsilon> v \<and> t \<noteq> y"
      using sep[rule_format, of "\<lambda> \<Xi>. \<Xi> 0 \<noteq> \<Xi> 1" v "undefined(1:=y)"] by auto 
      have "v' \<epsilon> w'"
        using \<open>v \<epsilon> w\<close> v' w' by auto
      have "wmax' \<subseteq>\<^sub>M v'"
        using \<open>wmax' \<subseteq>\<^sub>M v\<close> \<open>\<not> y \<epsilon> wmax'\<close> unfolding setext[of _ v] v' set_defs by blast
      hence "wmax' = v'"
        using wmax' \<open>v' \<epsilon> w'\<close> unfolding  proper_subset_def' by blast
      have "v = wmax' \<union>\<^sub>M {y}\<^sub>M"
        using \<open>wmax' \<noteq> v\<close> unfolding \<open>wmax' = v'\<close> setext[of v] setext[of _ v] set_defs v' by blast 
      then show False
        using \<open>\<not> wmax' \<union>\<^sub>M {y}\<^sub>M \<epsilon> w\<close> \<open>v \<epsilon> w\<close> by blast
      qed
    thus ?thesis
      using \<open>wmax' \<epsilon> w\<close> by blast
  qed
qed

lemma SP_unique_image [simp]: "SetProperty (\<lambda>x. \<forall>a b c. \<langle>b,a\<rangle> \<epsilon> x \<and> \<langle>c,a\<rangle> \<epsilon> x \<longrightarrow> b = c)"
  unfolding set_defs logsimps SetProperty_def by rule+

lemma SP_injective [simp]: "SetProperty (\<lambda>x. \<forall>a b c. \<langle>a,b\<rangle> \<epsilon> x \<and> \<langle>a,c\<rangle> \<epsilon> x \<longrightarrow> b = c)"
  unfolding set_defs logsimps SetProperty_def by rule+

lemma SFP_compose [simp,intro]: "SetFormulaPredicate (\<lambda> \<Xi>. \<exists>a b c. \<langle>a,b\<rangle> \<epsilon> \<Xi> k \<and> \<langle>b,c\<rangle> \<epsilon> \<Xi> l \<and> \<Xi> m = \<langle>a,c\<rangle>)"
proof-
  have sfp: "SetFormulaPredicate (\<lambda> \<Xi>. \<langle>\<Xi> (k+l+m+3),\<Xi> (k+l+m+4)\<rangle> \<epsilon> \<Xi> k \<and> \<langle>\<Xi> (k+l+m+4),\<Xi> (k+l+m+5)\<rangle> \<epsilon> \<Xi> l \<and> \<Xi> m = \<langle>\<Xi> (k+l+m+3), \<Xi> (k+l+m+5)\<rangle>)"
    unfolding logsimps by rule+
  show ?thesis
    using SFP_ex[OF SFP_ex[OF SFP_ex], of _ "k+l+m+3" "k+l+m+4" "k+l+m+5", OF sfp] by simp 
qed

lemma SP_function[simp]: "SetProperty (\<lambda> x. functionM x)"
  unfolding SetProperty_def set_defs logsimps by rule+

lemma SP_one_one[simp]: "SetProperty (\<lambda> x. one_oneM x)"
  unfolding SetProperty_def set_defs logsimps by rule+

lemma ordered_pair_mem: assumes "v \<epsilon> x" "v' \<epsilon> y" shows "\<langle>v,v'\<rangle> \<epsilon> \<PP> (\<PP> (x \<union>\<^sub>M y))"
proof-
  have "{v}\<^sub>M \<epsilon> \<PP> (x \<union>\<^sub>M y)" "{v,v'}\<^sub>M \<epsilon> \<PP> (x \<union>\<^sub>M y)"
    using \<open>v \<epsilon> x\<close> \<open>v' \<epsilon> y\<close> unfolding set_defs by blast+
  thus ?thesis
    unfolding setext[of _ "\<PP> _"] powerset_def'[of _ "\<PP> _"]
      pair_def' subsetM_def ordered_pairM_def  by blast
qed

lemma sing_eq_iff: "{a}\<^sub>M = {b}\<^sub>M \<longleftrightarrow> a = b"
  unfolding setext[of "{_}\<^sub>M"] singleton_def' by metis 

lemma sing_eq_pair_iff: "{a}\<^sub>M = {b,c}\<^sub>M \<longleftrightarrow> a = b \<and> b = c" 
  unfolding setext[of "{_}\<^sub>M"] pair_def' singleton_def' by metis 

lemma sing_eq_pair_iff': "{b,c}\<^sub>M = {a}\<^sub>M \<longleftrightarrow> a = b \<and> b = c" 
  using sing_eq_pair_iff by metis

lemma ordered_pair_unique[simp]: "\<langle>u,v\<rangle> = \<langle>u',v'\<rangle> \<longleftrightarrow> u = u' \<and> v = v'"
  unfolding setext[of "{_,_}\<^sub>M"] ordered_pairM_def using pair_def' singleton_def' by metis 

lemma ordered_pair_mem_union: assumes "\<langle>u,v\<rangle> \<epsilon> r" shows "u \<epsilon> \<Union>\<^sub>M (\<Union>\<^sub>M r)" "v \<epsilon> \<Union>\<^sub>M (\<Union>\<^sub>M r)"
proof-
  have "(\<langle>u,v\<rangle> \<epsilon> r \<and> {u,v}\<^sub>M \<epsilon> \<langle>u,v\<rangle>) \<and> u \<epsilon> {u,v}\<^sub>M" "(\<langle>u,v\<rangle> \<epsilon> r \<and> {u,v}\<^sub>M \<epsilon> \<langle>u,v\<rangle>) \<and> v \<epsilon> {u,v}\<^sub>M"
    using assms unfolding pair_def' ordered_pairM_def by blast+
  then show "u \<epsilon> \<Union>\<^sub>M (\<Union>\<^sub>M r)" "v \<epsilon> \<Union>\<^sub>M (\<Union>\<^sub>M r)" 
    unfolding union_def' by blast+
qed

lemma car_prod_ex: "\<exists> z. \<forall> u. u \<epsilon> z \<longleftrightarrow> u \<epsilon> \<PP> (\<PP> (x \<union>\<^sub>M y)) \<and> (\<exists> v v'. v \<epsilon> x \<and> v' \<epsilon> y \<and> u = \<langle>v,v'\<rangle>)"
proof-
  have sfp1: "SetFormulaPredicate (\<lambda>\<Xi>. (\<forall>z. \<not> \<Xi> m \<epsilon> \<Xi> 2 \<or> \<Xi> 0 \<noteq> \<langle>\<Xi> m,z\<rangle>))" for m
    unfolding logsimps by rule+
  have "SetFormulaPredicate (\<lambda>\<Xi>. \<exists>z. z \<epsilon> \<Xi> 1 \<and> (\<exists>v'. v' \<epsilon> \<Xi> 2 \<and> \<Xi> 0 = \<langle>z,v'\<rangle>))"
    by (rule SFP_ex[of "\<lambda> \<Xi>. \<Xi> 4 \<epsilon> \<Xi> 1 \<and> (\<exists>v'. v' \<epsilon> \<Xi> 2 \<and> \<Xi> 0 = \<langle>\<Xi> 4,v'\<rangle>)" 4, simplified fun_upd_same fun_upd_other]) (unfold logsimps, rule+)
  hence "SetFormulaPredicate (\<lambda>\<Xi>. \<exists>v v'. v \<epsilon> \<Xi> 1 \<and> v' \<epsilon> \<Xi> 2 \<and> \<Xi> 0 = \<langle>v,v'\<rangle>)"
    by simp
  from sep[rule_format, of "\<lambda> \<Xi>. \<exists> v v'. v \<epsilon> \<Xi> 1 \<and> v' \<epsilon> \<Xi> 2 \<and> \<Xi> 0 = \<langle>v,v'\<rangle>" "\<PP> (\<PP> (x \<union>\<^sub>M y))" "undefined(1:=x,2:=y)", OF this, simplified] sep
  show ?thesis
    by simp
qed

lemma car_prod_def': "u \<epsilon> x \<times>\<^sub>M y \<longleftrightarrow> (\<exists> v v'.  v \<epsilon> x \<and> v' \<epsilon> y \<and>  u = \<langle>v,v'\<rangle>)"
  unfolding cartesian_productM_def[rule_format] separationM_def
  using collect_def_ex[OF car_prod_ex, of _ x y] ordered_pair_mem by blast

lemma rel_inv_def': "u \<epsilon> rel_inverseM r \<longleftrightarrow> (\<exists> a b. \<langle>a,b\<rangle> \<epsilon> r \<and> u = \<langle>b,a\<rangle>)"
proof-
  have SR: "SetRelation (\<lambda>u r. \<exists>a b. \<langle>a,b\<rangle> \<epsilon> r \<and> u = \<langle>b,a\<rangle>)"
    unfolding SetRelation_def logsimps by rule+ 
   have eq: "(u \<epsilon> \<Union>\<^sub>M (\<Union>\<^sub>M r) \<times>\<^sub>M \<Union>\<^sub>M (\<Union>\<^sub>M r) \<and> (\<exists>a b. \<langle>a,b\<rangle> \<epsilon> r \<and> u = \<langle>b,a\<rangle>))
            \<longleftrightarrow> (\<exists>a b. \<langle>a,b\<rangle> \<epsilon> r \<and> u = \<langle>b,a\<rangle>)" for u
    unfolding car_prod_def'[rule_format] using ordered_pair_mem_union by blast 
    show ?thesis
      unfolding rel_inverseM_def 
      using collect_def_ex[of "\<lambda> v. (\<exists> a b. \<langle>a,b\<rangle> \<epsilon> r \<and> v = \<langle>b,a\<rangle>)"]
      sep_sr[rule_format,OF SR, of "\<Union>\<^sub>M (\<Union>\<^sub>M r) \<times>\<^sub>M \<Union>\<^sub>M (\<Union>\<^sub>M r)" r, unfolded eq] by simp
qed

lemma rng_def': "u \<epsilon> rngM r \<longleftrightarrow> (\<exists>v. \<langle>v,u\<rangle> \<epsilon> r)" 
proof-
  have ex: " \<exists>w. \<forall>u. (u \<epsilon> w) = (u \<epsilon> \<Union>\<^sub>M (\<Union>\<^sub>M r) \<and> (\<exists>v. \<langle>v,u\<rangle> \<epsilon> r))"
    by (rule sep_sr[rule_format, of "\<lambda> u r.\<exists>v. \<langle>v,u\<rangle> \<epsilon> r"  "\<Union>\<^sub>M (\<Union>\<^sub>M r)" r])
    (unfold SetRelation_def logsimps, rule+)
  have aux: "u \<epsilon> rngM r \<longleftrightarrow> (u \<epsilon> \<Union>\<^sub>M (\<Union>\<^sub>M r) \<and> (\<exists>v. \<langle>v,u\<rangle> \<epsilon> r))" (is "u \<epsilon> rngM r \<longleftrightarrow> (u  \<epsilon> ?S \<and> ?P u)")
    unfolding rngM_def separationM_def by (rule collect_def_ex[of "\<lambda> u .(u  \<epsilon> ?S \<and> ?P u)", folded domM_def]) fact
  show ?thesis
    unfolding aux using ordered_pair_mem_union by blast
qed

lemma dom_def': "u \<epsilon> domM r \<longleftrightarrow> (\<exists>v. \<langle>u,v\<rangle> \<epsilon> r)" 
proof-
  have ex: "\<exists>w. \<forall>u. (u \<epsilon> w) = (u \<epsilon> \<Union>\<^sub>M (\<Union>\<^sub>M r) \<and> (\<exists>v. \<langle>u,v\<rangle> \<epsilon> r))"
    by (rule sep_sr[rule_format, of "\<lambda> u r.\<exists>v. \<langle>u,v\<rangle> \<epsilon> r"  "\<Union>\<^sub>M (\<Union>\<^sub>M r)" r]) 
    (unfold SetRelation_def logsimps, rule+)
  have aux: "u \<epsilon> domM r \<longleftrightarrow> (u \<epsilon> \<Union>\<^sub>M (\<Union>\<^sub>M r) \<and> (\<exists>v. \<langle>u,v\<rangle> \<epsilon> r))" (is "u \<epsilon> domM r \<longleftrightarrow> (u  \<epsilon> ?S \<and> ?P u)")
    unfolding domM_def separationM_def by (rule collect_def_ex[of "\<lambda> u .(u  \<epsilon> ?S \<and> ?P u)"]) fact
  show ?thesis
    unfolding aux using ordered_pair_mem_union by blast
qed

lemma SFP_dom[simp, intro]: "SetFormulaPredicate (\<lambda> \<Xi>. \<Xi> k = domM (\<Xi> l))"
  unfolding set_defs
proof-
  have sr: "SetRelation (\<lambda>u w. \<exists> z. \<langle>u,z\<rangle> \<epsilon> w)"
    unfolding SetRelation_def logsimps by rule+
  show "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> k = separationM (\<Union>\<^sub>M (\<Union>\<^sub>M (\<Xi> l))) (\<lambda>u. \<exists>v. \<langle>u,v\<rangle> \<epsilon> \<Xi> l))"
    unfolding setext separ_def_sr[of "\<lambda>u w. \<exists> z. \<langle>u,z\<rangle> \<epsilon> w", OF sr]
    unfolding set_defs logsimps by rule+
qed

lemma SFP_rng[simp, intro]: "SetFormulaPredicate (\<lambda> \<Xi>. \<Xi> k = rngM (\<Xi> l))"
  unfolding set_defs 
proof-
  have sr: "SetRelation (\<lambda>u w. \<exists> z. \<langle>z,u\<rangle> \<epsilon> w)"
    unfolding SetRelation_def logsimps by rule+
  show "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> k = separationM (\<Union>\<^sub>M (\<Union>\<^sub>M (\<Xi> l))) (\<lambda>u. \<exists>v. \<langle>v,u\<rangle> \<epsilon> \<Xi> l))"
    unfolding setext separ_def_sr[of "\<lambda>u w. \<exists> z. \<langle>z,u\<rangle> \<epsilon> w", OF sr]
    unfolding set_defs logsimps by rule+
qed

lemmas[intro] = SFP_rng[unfolded set_defs logsimps] SFP_dom[unfolded set_defs logsimps]

lemma "SetRelation (\<lambda>x y. \<exists>f. one_oneM f \<and> x = domM f \<and> y = rngM f)"
    (is "SetRelation (\<lambda> x y. (\<exists> f. ?P x y f))")
proof-
  have "SetRelation (\<lambda> x y. x = domM y)"
    unfolding SetRelation_def by simp
  term ?P
  let ?P = "\<lambda> x y f. one_oneM f \<and> x = domM f \<and> y = rngM f"
  show "SetRelation (\<lambda> x y. (\<exists> f. ?P x y f))"
    unfolding set_defs logsimps SetRelation_def by rule+
qed

lemma SR_equiv[simp]: "SetRelation (\<lambda> x y. x \<approx>\<^sub>M y)"
  unfolding SetRelation_def  set_defs logsimps by rule+

lemma SP_dedekind[simp]: "SetProperty dedekind_fin"
  unfolding SetProperty_def dedekind_fin_def one_oneM_def set_equivalent_def set_defs logsimps by rule+

lemma rel_inv_dom_rng: "domM (rel_inverseM r) = rngM r" "rngM (rel_inverseM r) = domM r"
  unfolding setext[of _ "rngM _"] setext[of _ "domM _"] dom_def' rng_def' rel_inv_def' ordered_pair_unique by blast+

lemma rel_inv_rel: "relationM f \<Longrightarrow> relationM (rel_inverseM f)"
  unfolding relationM_def rel_inv_def' by blast  

lemma one_one_inv: "one_oneM f \<Longrightarrow> one_oneM (rel_inverseM f)"
  unfolding one_oneM_def rel_inv_def' functionM_def ordered_pair_unique using rel_inv_rel by auto

lemma fun_inj: "functionM f \<Longrightarrow> \<langle>a,b\<rangle> \<epsilon> f \<Longrightarrow> \<langle>a,c\<rangle> \<epsilon> f \<Longrightarrow>  b = c"
  unfolding functionM_def by blast

lemma one_one_inj: "one_oneM f \<Longrightarrow> \<langle>b,a\<rangle> \<epsilon> f \<Longrightarrow> \<langle>c,a\<rangle> \<epsilon> f \<Longrightarrow>  b = c"
  unfolding one_oneM_def by blast

lemma set_equivalent_sym: "x \<approx>\<^sub>M y \<longleftrightarrow> y \<approx>\<^sub>M x"
proof-
  have "x \<approx>\<^sub>M y \<Longrightarrow>  y \<approx>\<^sub>M x" for x y
  proof-
    assume "x \<approx>\<^sub>M y"
    then obtain f where f : "one_oneM f" "x = domM f" "y = rngM f"     
      unfolding set_equivalent_def by blast
    show "y \<approx>\<^sub>M x"
      unfolding set_equivalent_def 
      by (rule exI[of _ "rel_inverseM f"]) (simp add: one_one_inv[OF \<open>one_oneM f\<close>] f(2,3) rel_inv_dom_rng) 
  qed
  thus ?thesis 
    by blast
qed

lemma compose_def': "u \<epsilon> f \<circ>\<^sub>M g \<longleftrightarrow> (\<exists>a b c. \<langle>a,b\<rangle> \<epsilon> g \<and> \<langle>b,c\<rangle> \<epsilon> f \<and> u = \<langle>a,c\<rangle>)" 
proof-
  have ex: "\<exists>w. \<forall>u. (u \<epsilon> w) = (u \<epsilon> domM g \<times>\<^sub>M rngM f  \<and> (\<exists>a b c. \<langle>a,b\<rangle> \<epsilon> g \<and> \<langle>b,c\<rangle> \<epsilon> f \<and> u = \<langle>a,c\<rangle>))"
    using sep[rule_format, OF SFP_compose[of 1 2 0], of "domM g \<times>\<^sub>M rngM f" "undefined(1:=g, 2:= f)"] 
    by simp
  have aux: "u \<epsilon> f \<circ>\<^sub>M g \<longleftrightarrow> (u \<epsilon> domM g \<times>\<^sub>M rngM f) \<and> (\<exists>a b c. \<langle>a,b\<rangle> \<epsilon> g \<and> \<langle>b,c\<rangle> \<epsilon> f \<and> u = \<langle>a,c\<rangle>)" (is "u \<epsilon> f \<circ>\<^sub>M g \<longleftrightarrow> u \<epsilon> ?S \<and> ?Q u")
    unfolding composeM_def separationM_def 
    by (rule collect_def_ex[of "\<lambda> u. (u \<epsilon> ?S \<and> ?Q u)"]) fact
  show ?thesis
    unfolding aux car_prod_def' dom_def'[of _ g] rng_def'[of _ f]  by blast 
qed  

lemma rel_comp: assumes "relationM f" "relationM g" shows "relationM (f \<circ>\<^sub>M g)"
  using assms unfolding relationM_def compose_def' by blast

lemma fun_comp: assumes "functionM f" "functionM g" shows "functionM (f \<circ>\<^sub>M g)"
  using assms rel_comp unfolding functionM_def  compose_def' ordered_pair_unique by blast 

lemma one_one_comp: assumes "one_oneM f" "one_oneM g" shows "one_oneM (f \<circ>\<^sub>M g)"
  using assms fun_comp unfolding one_oneM_def  compose_def' ordered_pair_unique by blast  

lemma set_equivalent_trans: assumes "x \<approx>\<^sub>M y" "y \<approx>\<^sub>M z" shows "x \<approx>\<^sub>M z"
proof-
  obtain f1 where f1: "one_oneM f1" and  "x = domM f1" "y = rngM f1"
    using \<open>x \<approx>\<^sub>M y\<close> unfolding set_equivalent_def by blast
  obtain f2 where f2: "one_oneM f2" and "y = domM f2" "z = rngM f2"
    using \<open>y \<approx>\<^sub>M z\<close> unfolding set_equivalent_def by blast
  have "one_oneM (f2 \<circ>\<^sub>M f1)"
    using f1 f2 one_one_comp by blast
  have "x = domM (f2 \<circ>\<^sub>M f1)"
     unfolding dom_def'  setext unfolding compose_def' ordered_pair_unique
   proof (rule, rule)
     fix u assume "\<exists>v a b c. \<langle>a,b\<rangle> \<epsilon> f1 \<and> \<langle>b,c\<rangle> \<epsilon> f2 \<and> u = a \<and> v = c"
     then show "u \<epsilon> x"
       unfolding \<open>x = domM f1\<close>[unfolded setext dom_def', rule_format] by blast
   next
     fix u assume "u \<epsilon> x"
     then obtain b where \<open>\<langle>u,b\<rangle> \<epsilon> f1\<close> "b \<epsilon> y"
       unfolding \<open>x = domM f1\<close>[unfolded setext dom_def', rule_format]
                 \<open>y = rngM f1\<close>[unfolded setext rng_def', rule_format] by blast
     then obtain c where \<open>\<langle>b,c\<rangle> \<epsilon> f2\<close> "c \<epsilon> z"
       unfolding \<open>y = domM f2\<close>[unfolded setext dom_def', rule_format]
                 \<open>z = rngM f2\<close>[unfolded setext rng_def', rule_format] by blast
     show "\<exists>v a b c. \<langle>a,b\<rangle> \<epsilon> f1 \<and> \<langle>b,c\<rangle> \<epsilon> f2 \<and> u = a \<and> v = c"
       using \<open>\<langle>u,b\<rangle> \<epsilon> f1\<close> \<open>\<langle>b,c\<rangle> \<epsilon> f2\<close> by auto
   qed
  have "z = rngM (f2 \<circ>\<^sub>M f1)"
     unfolding rng_def'  setext unfolding compose_def' ordered_pair_unique
   proof (rule, rule)
     fix u assume "\<exists>v a b c. \<langle>a,b\<rangle> \<epsilon> f1 \<and> \<langle>b,c\<rangle> \<epsilon> f2 \<and> v = a \<and> u = c"
     then show "u \<epsilon> z"
       unfolding \<open>z = rngM f2\<close>[unfolded setext rng_def', rule_format] by blast
   next
     fix u assume "u \<epsilon> z"
     then obtain b where \<open>\<langle>b,u\<rangle> \<epsilon> f2\<close> "b \<epsilon> y"
       unfolding \<open>y = domM f2\<close>[unfolded setext dom_def', rule_format]
                 \<open>z = rngM f2\<close>[unfolded setext rng_def', rule_format] by blast
     then obtain c where \<open>\<langle>c,b\<rangle> \<epsilon> f1\<close> "c \<epsilon> x"
       unfolding \<open>x = domM f1\<close>[unfolded setext dom_def', rule_format]
                 \<open>y = rngM f1\<close>[unfolded setext rng_def', rule_format] by blast
     show "\<exists>v a b c. \<langle>a,b\<rangle> \<epsilon> f1 \<and> \<langle>b,c\<rangle> \<epsilon> f2 \<and> v = a \<and> u = c"
       using \<open>\<langle>b,u\<rangle> \<epsilon> f2\<close> \<open>\<langle>c,b\<rangle> \<epsilon> f1\<close> by auto
   qed
  show ?thesis
      unfolding set_equivalent_def
      using \<open>one_oneM (f2 \<circ>\<^sub>M f1)\<close> \<open>x = domM (f2 \<circ>\<^sub>M f1)\<close> \<open>z = rngM (f2 \<circ>\<^sub>M f1)\<close> by blast 
qed

lemma regular_suc: assumes "regular x" "regular y" 
  shows "regular (x \<union>\<^sub>M {y}\<^sub>M)"
  unfolding regular_def pow_setsuc_def' 
  oops
\<comment> \<open>not true, consider \<open>{x} \<epsilon> x\<close>\<close>

lemma regular_suc: assumes "transM x" "regular x" "regular y"
  shows "regular (x \<union>\<^sub>M {y}\<^sub>M)"
proof (cases "y \<epsilon> x")
  assume "y \<epsilon> x"
  hence "x \<union>\<^sub>M {y}\<^sub>M = x"
    unfolding setext[of _ x] set_defs by blast
  thus "regular (x \<union>\<^sub>M {y}\<^sub>M)"
    using \<open>regular x\<close> by simp
next
  assume "\<not> y \<epsilon> x" 
  show "regular (x \<union>\<^sub>M {y}\<^sub>M)"
    unfolding regular_def 
  proof (rule, rule, rule)
    fix w 
    assume "w \<subseteq>\<^sub>M x \<union>\<^sub>M {y}\<^sub>M" "\<exists> z. z \<epsilon> w"
    obtain w' where w': "\<And> z. z \<epsilon> w' \<longleftrightarrow> z \<epsilon> w \<and> z \<noteq> y"
      using sep_sr[of "\<lambda> x y. x \<noteq> y"] unfolding SetRelation_def by force
    have  "w' \<subseteq>\<^sub>M x"
      using \<open>w \<subseteq>\<^sub>M x \<union>\<^sub>M {y}\<^sub>M\<close> w' subsetM_def by auto
    show "\<exists>z. z \<epsilon> w \<and> (\<forall>v. \<not> (v \<epsilon> z \<and> v \<epsilon> w))"
    proof (cases "y \<epsilon> w")
      assume "y \<epsilon> w"
      show ?thesis
      proof (cases "w' = \<emptyset>")
        assume "w' = \<emptyset>"
        have "w = {y}\<^sub>M"
          using w' empty_is_empty \<open>y \<epsilon> w\<close> unfolding setext[of w] set_defs \<open>w' = \<emptyset>\<close> by blast
        hence "y \<epsilon> w \<and> (\<forall>v. \<not> (v \<epsilon> y \<and> v \<epsilon> w))"
          unfolding \<open>w = {y}\<^sub>M\<close> set_defs  using regular_not_self_mem[OF \<open>regular y\<close>] by blast
        then show ?thesis
          by blast
      next
        assume "\<not> w' = \<emptyset>"
        hence "\<exists> z. z \<epsilon> w'"
          by (simp add: empty_set_def')
        from \<open>regular x\<close>[unfolded regular_def, rule_format, OF \<open>w' \<subseteq>\<^sub>M x\<close> this]
        obtain m where "m \<epsilon> w'" and m: "\<forall>v. \<not> (v \<epsilon> m \<and> v \<epsilon> w')"
          by blast
        hence "m \<epsilon> w"
          using w' by blast
        have "\<not> y \<epsilon> m"
          using \<open>transM x\<close>[unfolded transM_def] \<open>m \<epsilon> w'\<close> \<open>w' \<subseteq>\<^sub>M x\<close> \<open>\<not> y \<epsilon> x\<close> subsetM_def by blast
        have "\<forall>v. \<not> (v \<epsilon> m \<and> v \<epsilon> w)"
          using m unfolding w' using \<open>\<not> y \<epsilon> m\<close> by blast 
        then show ?thesis
          using \<open>m \<epsilon> w\<close> by blast
      qed
    next
      assume "\<not> y \<epsilon> w"
      hence "w \<subseteq>\<^sub>M x"
        using \<open>w \<subseteq>\<^sub>M x \<union>\<^sub>M {y}\<^sub>M\<close> w' subsetM_def by auto  
      from \<open>regular x\<close>[unfolded regular_def, rule_format, OF this \<open>\<exists> z. z \<epsilon> w\<close>]
      show ?thesis.
    qed
  qed
qed

lemma epschain_suc_epschain: "epschain x \<Longrightarrow> epschain (x \<union>\<^sub>M {x}\<^sub>M)"
  unfolding set_defs by blast

lemma ord_suc_ord: "ordM x \<Longrightarrow> ordM (x \<union>\<^sub>M {x}\<^sub>M)"
  using regular_suc[of x] unfolding ordM_def epschain_def
  using trans_suc by auto  

lemma nat_suc_nat: "natM x \<Longrightarrow> natM (x \<union>\<^sub>M {x}\<^sub>M)"
  unfolding natM_def using ord_suc_ord tarski_suc_tarski by blast

lemma intersect_transM: assumes "transM x" "transM y"
  shows "transM (x \<inter>\<^sub>M y)"
  using assms unfolding intersection_def' transM_def subsetM_def by blast

lemma intersect_epsachain: assumes "epschain x" "epschain y"
  shows "epschain (x \<inter>\<^sub>M y)"
  using assms intersect_transM unfolding intersection_def' epschain_def subsetM_def by blast

lemma intersect_regular: assumes "regular x" "regular y"
  shows "regular (x \<inter>\<^sub>M y)"
  using assms unfolding regular_def intersection_def' subsetM_def by blast

lemma intersect_ordM: assumes "ordM x" "ordM y"
  shows "ordM (x \<inter>\<^sub>M y)"
  using assms intersect_transM intersect_regular  unfolding ordM_def
  unfolding  intersection_def' epschain_def by simp

lemma intersect_natM: assumes "natM x" "natM y"
  shows "natM (x \<inter>\<^sub>M y)"
  using assms intersect_ordM tarski_subset_tarski intersect_subset(1) unfolding natM_def by blast

lemma one_natM[simp]: "natM ({\<emptyset>}\<^sub>M)"
  using nat_suc_nat[OF emp_natM] by simp

lemma mem_ord_ord: assumes "u \<epsilon> v" "ordM v" shows "ordM u"
  unfolding ordM_def epschain_def conj_assoc[symmetric]
proof (rule, rule)
  have "regular v" "u \<subseteq>\<^sub>M v"
    using \<open>ordM v\<close> ordM_D1 \<open>u \<epsilon> v\<close> ordM_def by blast+
  then show "regular u"
    unfolding regular_def using subsetM_trans[OF _ \<open>u \<subseteq>\<^sub>M v\<close>] by blast
  have "u \<subseteq>\<^sub>M v" "epschain v" "regular v" "transM v"
    using assms unfolding natM_def ordM_def transM_def epschain_def by blast+
  thus "\<forall>y z. y \<epsilon> u \<and> z \<epsilon> u \<longrightarrow> y \<epsilon> z \<or> y = z \<or> z \<epsilon> y"
    using \<open>ordM v\<close> unfolding ordM_def subsetM_def epschain_def by blast
  show "transM u"
    unfolding transM_def set_defs
  proof (rule, rule, rule, rule)
    fix z y
    assume "y \<epsilon> u" "z \<epsilon> y"
    hence "z \<epsilon> v" "y \<epsilon> v" 
      using \<open>u \<epsilon> v\<close> \<open>transM v\<close> unfolding transM_def set_defs by blast+
    have "u \<noteq> z"
      using regular_antisym_mem[OF \<open>regular v\<close> \<open>y \<epsilon> v\<close> \<open>z \<epsilon> v\<close>] \<open>y \<epsilon> u\<close> \<open>z \<epsilon> y\<close> by blast
    have "\<not> u \<epsilon> z"
      using regular_antisym2_mem[OF \<open>regular v\<close> \<open>u \<epsilon> v\<close> \<open>z \<epsilon> v\<close> \<open>y \<epsilon> v\<close>] \<open>y \<epsilon> u\<close> \<open>z \<epsilon> y\<close> by blast
    show "z \<epsilon> u"
      using ordM_D2[OF \<open>ordM v\<close> \<open>u \<epsilon> v\<close> \<open>z \<epsilon> v\<close>] \<open>u \<noteq> z\<close> \<open>\<not> u \<epsilon> z\<close> by blast
  qed
qed   

lemma mem_nat_nat: assumes "u \<epsilon> v" "natM v" shows "natM u"
  unfolding natM_def 
proof
  show "ordM u"
    using assms mem_ord_ord unfolding natM_def by blast
  have "u \<subseteq>\<^sub>M v"
    using assms unfolding natM_def ordM_def transM_def epschain_def by blast
  thus "tarski_fin u"
    using \<open>natM v\<close>tarski_subset_tarski unfolding natM_def by blast
qed    

lemma ordinal_subset_mem: assumes "ordM x" "ordM y" "y \<subset>\<^sub>M x"
  shows "y \<epsilon> x"
proof-
  have SR: "SetRelation (\<lambda> v y. \<not> v \<epsilon> y)" 
    unfolding SetRelation_def by simp
  have "regular x"
    using \<open>ordM x\<close> by simp 
  have dif: "u \<epsilon> separationM x (\<lambda> v. \<not> v \<epsilon> y) \<longleftrightarrow> u \<epsilon> x \<and> \<not> u \<epsilon> y" for u
    using separ_def_sr[OF SR].
  hence "separationM  x (\<lambda> v. \<not> v \<epsilon> y) \<subseteq>\<^sub>M x"
    unfolding subsetM_def by blast
  from \<open>regular x\<close>[unfolded regular_def, rule_format, OF this, unfolded dif]
  obtain c where "c \<epsilon> x" "\<not> c \<epsilon> y" and c: "\<forall>v. v \<epsilon> c \<longrightarrow> (v \<epsilon> y \<or> \<not> v \<epsilon> x)"
    using  proper_subset_diff[OF \<open>y \<subset>\<^sub>M x\<close>] by blast 
  have "c \<subseteq>\<^sub>M x"
    using \<open>c \<epsilon> x\<close> assms(1) natM_def ordM_D1 by blast
  hence "c \<subseteq>\<^sub>M y"
    using \<open>y \<subset>\<^sub>M x\<close> c unfolding subsetM_def proper_subsetM_def by blast 
  have "y = c"
  proof (rule subsetM_antisym[OF \<open>c \<subseteq>\<^sub>M y\<close>], unfold subsetM_def, rule, rule)
    fix z assume "z \<epsilon> y"   
    hence "z \<epsilon> x" 
      using \<open>y \<subset>\<^sub>M x\<close> unfolding proper_subsetM_def by blast
    from ordM_D2[OF \<open>ordM x\<close> this \<open>c \<epsilon> x\<close>]
    show "z \<epsilon> c"
      using \<open>\<not> c \<epsilon> y\<close> \<open>z \<epsilon> y\<close> ordM_D1[OF \<open>ordM y\<close> \<open>z \<epsilon> y\<close>, unfolded subsetM_def] by blast
  qed
  thus ?thesis  
    using \<open>c \<epsilon> x\<close> by blast
qed

lemma ordM_total: assumes "ordM x" "ordM y"
  shows "x \<epsilon> y \<or> y \<epsilon> x \<or> x = y"
  using ordM_def[unfolded epschain_def]
proof-
  have "regular (x \<inter>\<^sub>M y)"
    using intersect_ordM[OF \<open>ordM x\<close> \<open>ordM y\<close>] by simp
  from regular_not_self_mem[OF this]
  have "\<not> (x \<inter>\<^sub>M y \<subset>\<^sub>M x \<and> x \<inter>\<^sub>M y \<subset>\<^sub>M y)"
      using ordinal_subset_mem[OF assms(1) intersect_ordM, OF assms]  
            ordinal_subset_mem[OF assms(2) intersect_ordM, OF assms]
       unfolding intersection_def' by blast
     with sep_sr[rule_format, of "\<lambda> v y. v \<epsilon> y"]
     consider "x \<inter>\<^sub>M y = x" | "x \<inter>\<^sub>M y = y" 
       unfolding proper_subsetM_def using intersection_def' by blast  
  then show ?thesis
  proof (cases)
    assume "x \<inter>\<^sub>M y = x"
    hence "x = y \<or> x \<subset>\<^sub>M y"
      unfolding proper_subsetM_def setext using intersection_def' by blast
    with ordinal_subset_mem[OF assms(2,1)] 
    show ?thesis
      by blast
  next
    assume "x \<inter>\<^sub>M y = y"
    hence "x = y \<or> y \<subset>\<^sub>M x"
      unfolding proper_subsetM_def setext using intersection_def' by blast
    with ordinal_subset_mem[OF assms] 
    show ?thesis
      by blast
  qed
qed

lemma ordM_trans: assumes "ordM v"  "w \<epsilon> u" "u \<epsilon> v"  shows "w \<epsilon> v"
  using assms ordM_D1 subsetM_def by blast

lemma ord_mem_suc: assumes "ordM x" and "y \<epsilon> x" 
  shows  "y \<union>\<^sub>M {y}\<^sub>M \<epsilon> x \<or> y \<union>\<^sub>M {y}\<^sub>M = x"
proof-
  have "ordM y"
    using mem_ord_ord[OF \<open>y \<epsilon> x\<close> \<open>ordM x\<close>].
  thm ordM_regular
  have "y \<epsilon> y \<union>\<^sub>M {y}\<^sub>M"
    unfolding set_defs by blast 
  from regular_antisym2_mem[OF ordM_regular, OF \<open>ordM x\<close>]  ordM_total[OF  \<open>ordM x\<close>]
  show ?thesis
    by (metis \<open>ordM y\<close> assms(2) ordM_trans ord_suc_ord pow_setsuc_def')
qed

lemma all_nat_suc: assumes "natM x" "x \<noteq> \<emptyset>"
  shows "\<exists> y. x = y \<union>\<^sub>M {y}\<^sub>M"
proof-
  from natM_D1[OF \<open>natM x\<close>]
  have "\<forall>z. z \<epsilon> x \<longrightarrow> z \<subseteq>\<^sub>M x"
    using ordM_D1 by blast 
  have "\<exists>z. z \<epsilon> x"
    using  \<open>x \<noteq> \<emptyset>\<close> by (simp add: empty_set_def')
  from  natM_D2[OF \<open>natM x\<close>, unfolded tarski_fin_def, rule_format, of x, OF ordM_D1[OF natM_D1[OF \<open>natM x\<close>]] \<open>\<exists>z. z \<epsilon> x\<close>]
  obtain y where y: "y \<epsilon> x" "(\<nexists>w. w \<epsilon> x \<and> y \<subset>\<^sub>M w)"
    by fast
  have "y \<noteq> y \<union>\<^sub>M {y}\<^sub>M"
    using regular_antisym2_mem[OF ordM_regular[OF natM_D1[OF \<open>natM x\<close>]]] pow_setsuc_def' y(1) by metis
  have "y \<subseteq>\<^sub>M y \<union>\<^sub>M {y}\<^sub>M"
    unfolding set_defs by blast
  hence "y \<subset>\<^sub>M y \<union>\<^sub>M {y}\<^sub>M"
    using \<open>y \<noteq> y \<union>\<^sub>M {y}\<^sub>M\<close>proper_subsetI by blast 
  hence "\<not> y \<union>\<^sub>M {y}\<^sub>M \<epsilon> x"
    using y by blast
  then show ?thesis
    using ord_mem_suc[OF \<open>ordM x\<close> \<open>y \<epsilon> x\<close>] by blast
qed

lemma set_of_ords_regular: assumes "\<forall> y. y \<epsilon> s \<longrightarrow> ordM y"
  shows "regular s"   
  unfolding regular_def
proof (rule, rule, rule)
  fix y assume "y \<subseteq>\<^sub>M s" "\<exists>z. z \<epsilon> y"
  then obtain z where "z \<epsilon> y"
    by blast
  have "ordM z"
    by (meson \<open>y \<subseteq>\<^sub>M s\<close> \<open>z \<epsilon> y\<close> assms mem_ord_ord subsetM_def union_def')
  hence "regular z"
    by simp
  show "\<exists>u. u \<epsilon> y \<and> (\<forall>v. \<not> (v \<epsilon> u \<and> v \<epsilon> y))"
  proof (cases "\<forall>v. \<not> (v \<epsilon> z \<and> v \<epsilon> y)", use \<open>z \<epsilon> y\<close> in blast)   
    assume a: "\<not> (\<forall>v. \<not> (v \<epsilon> z \<and> v \<epsilon> y))"
    from sep_sr[of "\<lambda> x y. x \<epsilon> y", rule_format, of z]
    obtain u where u: "\<forall> v. v \<epsilon> u \<longleftrightarrow> v \<epsilon> z \<and> v \<epsilon> y"
      unfolding SetRelation_def by auto
    hence "u \<subseteq>\<^sub>M z" "\<exists> v. v \<epsilon> u"
      using a unfolding u[rule_format] set_defs by blast+
    from \<open>regular z\<close>[unfolded regular_def, rule_format, OF this]
    obtain m where "m \<epsilon> u" "\<forall>v. \<not> (v \<epsilon> m \<and> v \<epsilon> u)" 
      by blast
    hence "m \<epsilon> y \<and> (\<forall>v. \<not> (v \<epsilon> m \<and> v \<epsilon> y))"
      unfolding u[rule_format] using \<open>ordM z\<close> ordM_trans by presburger
    thus ?thesis
      by blast
  qed
qed

lemma union_of_ords_regular: assumes "\<forall> y. y \<epsilon> s \<longrightarrow> ordM y"
  shows "regular (\<Union>\<^sub>M s)"
  using assms mem_ord_ord set_of_ords_regular union_def' by blast

lemma union_of_ords_ord: assumes "\<forall> y. y \<epsilon> s \<longrightarrow> ordM y"
  shows "ordM (\<Union>\<^sub>M s)"   
proof-
  have t: "transM (\<Union>\<^sub>M s)"
    using assms epschain_def ordM_def union_trans_trans by blast 
  have r: "regular (\<Union>\<^sub>M s)"
    by (simp add: assms union_of_ords_regular)
  have o: "ordM v" if "v \<epsilon> (\<Union>\<^sub>M s)" for v
    using assms(1) mem_ord_ord that union_def' by blast
  show "ordM (\<Union>\<^sub>M s)"
    unfolding ordM_def epschain_def using t r o ordM_total by blast
qed

lemma union_ord: assumes "ordM x" shows "ordM (\<Union>\<^sub>M x)"
  using assms mem_ord_ord union_of_ords_ord by blast

end

locale L_setext_empty_power_union_repl_reg  = L_setext + L_empty + L_power + L_union + L_repl + L_reg

begin
text \<open>Some consequences of the axiom of regularity\<close>

sublocale L_setext_empty_power_union_repl
  by unfold_locales

lemma mem_not_refl: "\<not> x \<epsilon> x"
 by (simp add: regular_not_self_mem)    

lemma mem_antisym: "\<not> (u \<epsilon> v \<and> v \<epsilon> u)"
  by (meson any_reg regular_antisym_mem setsuc)   

lemma  suc_unique:  assumes "c \<union>\<^sub>M {c}\<^sub>M = d \<union>\<^sub>M {d}\<^sub>M" 
  shows "c = d"
proof (rule ccontr)
  assume "c \<noteq> d"
  from assms[unfolded setext pow_setsuc_def'[of "_ \<union>\<^sub>M _"], unfolded pow_setsuc_def']
  have "c \<epsilon> d" "d \<epsilon> c"
    using \<open>c \<noteq> d\<close> by blast+
  thus False
    using mem_antisym by blast
qed

lemma mem_neq_singleton: "x \<noteq> {x}\<^sub>M"
  by (metis reg singleton_def')
   
lemma mem_antisym2: "\<not> (a \<epsilon> b \<and> b \<epsilon> c \<and> c \<epsilon> a)"
  using reg[rule_format, of "{a,b}\<^sub>M \<union>\<^sub>M {c}\<^sub>M", unfolded pair_def' pow_setsuc_def'] by blast

lemma suc_subset[simp]: "z \<subset>\<^sub>M z\<union>\<^sub>M{z}\<^sub>M"
  unfolding proper_subsetM_def  setext binunion_def'
  singleton_def' using mem_not_refl[of z] by blast

end

locale L_setext_empty_setsuc  = L_setext + L_empty + L_setsuc 

begin

sublocale L_setext_empty
 by unfold_locales

lemma setsuc_singletonM_ex: "\<exists> x. \<forall> u. u \<epsilon> x \<longleftrightarrow>  u = y"
  using setsuc[rule_format, of \<emptyset> y] empty_is_empty by simp

lemma setsuc_singleton_def': "u \<epsilon> {x}\<^sub>M \<longleftrightarrow>  u = x"
  using collect_def_ex[OF setsuc_singletonM_ex, folded singletonM_def]. 

lemma setsuc_def'[set_defs]: "u \<epsilon> x\<union>\<^sub>M{y}\<^sub>M \<longleftrightarrow> (u \<epsilon> x \<or> u = y)"
  using collect_def_ex[OF setsuc[rule_format]] unfolding binunionM_def setsuc_singleton_def'.


end 

subsection \<open>Negation of inf\<close>

locale L_setext_empty_power_union_repl_fin  = L_setext + L_empty + L_power + L_union + L_repl +  L_fin

begin

sublocale L_setext_empty_repl
     by unfold_locales

sublocale L_setext_empty
  by unfold_locales

sublocale L_setext_empty_power_union_repl
  by unfold_locales

lemma nat_induction_sfp: assumes "SetFormulaPredicate P" and  "P (\<Xi>(0:=\<emptyset>))" and "natM x" and
  step: "\<And> x. natM x \<Longrightarrow> P (\<Xi>(0:=x)) \<Longrightarrow> P (\<Xi>(0:=x \<union>\<^sub>M {x}\<^sub>M))"
  shows "P (\<Xi>(0:=x))"
proof (rule ccontr)
  assume "\<not> P (\<Xi>(0:=x))"
  define v where "v = separationM x (\<lambda> x. P(\<Xi>(0:=x)))"
  from separ_def_sfp[OF \<open>SetFormulaPredicate P\<close>]
  have v: "u \<epsilon> v \<longleftrightarrow> u \<epsilon> x \<and> P(\<Xi>(0:=u))" for u
    unfolding v_def by simp 
  hence "\<emptyset> \<epsilon> v"
    using \<open>P (\<Xi>(0:=\<emptyset>))\<close> \<open>\<not> P (\<Xi>(0:=x))\<close> \<open>natM x\<close> emp_natM empty_is_empty ordM_total unfolding natM_def by blast
  have "(y \<union>\<^sub>M {y}\<^sub>M) \<epsilon> v" if "y \<epsilon> v" for y
   unfolding v[of "y \<union>\<^sub>M {y}\<^sub>M"] using \<open>\<not> P (\<Xi>(0:=x))\<close> \<open>natM x\<close> that[unfolded v[of y]] step[of y] ord_mem_suc[of x y] mem_nat_nat[of y x] natM_D1[OF \<open>natM x\<close>] by fast
  thus False
    using \<open>\<emptyset> \<epsilon> v\<close> fin by auto
qed

lemma nat_induction_sp: assumes "SetProperty P" and  "P \<emptyset>" and "natM x" and
  step: "\<And> x. natM x \<Longrightarrow> P x \<Longrightarrow> P (x \<union>\<^sub>M {x}\<^sub>M)"
shows "P x"
  using assms unfolding SetProperty_def using nat_induction_sfp by force  

end

locale L_setext_empty_power_union_repl_reg_fin  = L_setext + L_empty + L_power + L_union + L_repl + L_reg + L_fin

begin

sublocale L_setext_empty_power_union_repl_fin
  by unfold_locales

sublocale L_setext_empty_power_union_repl_reg
  by unfold_locales


lemma SR_card: "SetRelation cardinality"
  unfolding set_defs logsimps SetRelation_def by rule+

lemma card_suc: assumes "\<not> y \<epsilon> x" "cardinality x m" shows "cardinality (x \<union>\<^sub>M {y}\<^sub>M)  (m \<union>\<^sub>M {m}\<^sub>M)"
proof-
  obtain f where "one_oneM f" "x = domM f" "m = rngM f" "natM m"
    using \<open>cardinality x m\<close> unfolding cardinality_def set_equivalent_def by blast
  let ?f = "f \<union>\<^sub>M {\<langle>y,m\<rangle>}\<^sub>M"
  have "natM (m \<union>\<^sub>M {m}\<^sub>M)"
    by (simp add: \<open>natM m\<close> nat_suc_nat)
  have "x \<union>\<^sub>M {y}\<^sub>M = domM ?f"
    using \<open>x = domM f\<close> unfolding setext dom_def' by auto
  have "m \<union>\<^sub>M {m}\<^sub>M = rngM ?f"
    using \<open>m = rngM f\<close> unfolding setext rng_def' by auto
  have "relationM ?f"
    unfolding relationM_def
    using \<open>one_oneM f\<close> functionM_def one_oneM_def relationM_def by auto 
  then have "functionM ?f"
    unfolding functionM_def
    using \<open>one_oneM f\<close> \<open>x = domM f\<close> \<open>\<not> y \<epsilon> x\<close> dom_def' fun_inj one_oneD3 by auto 
  then have "one_oneM ?f"
    unfolding one_oneM_def 
    using   \<open>\<not> y \<epsilon> x\<close> one_one_inj[OF \<open>one_oneM f\<close>] \<open>m = rngM f\<close> mem_not_refl[of m] 
    rng_def'  by auto 
  show ?thesis
    unfolding cardinality_def set_equivalent_def 
    using \<open>m \<union>\<^sub>M {m}\<^sub>M = rngM ?f\<close> \<open>natM (m \<union>\<^sub>M {m}\<^sub>M)\<close> \<open>one_oneM ?f\<close> \<open>x \<union>\<^sub>M {y}\<^sub>M = domM ?f\<close> by blast
qed                                    

lemma card_emp: "cardinality \<emptyset> \<emptyset>" 
proof-
  have "natM \<emptyset>"
    by simp
  moreover have "one_oneM \<emptyset>" 
    unfolding one_oneM_def functionM_def relationM_def by simp
  moreover have "\<emptyset> = domM \<emptyset>" "\<emptyset> = rngM \<emptyset>"                          
    unfolding setext dom_def' rng_def' by simp_all 
  ultimately show ?thesis
    unfolding cardinality_def set_equivalent_def 
    using exI[of "\<lambda> f.  one_oneM f \<and> \<emptyset> = domM f \<and> \<emptyset> = rngM f" \<emptyset>] by blast
qed

lemma dedekind_finite_suc: assumes "dedekind_fin x" shows "dedekind_fin (x \<union>\<^sub>M {t}\<^sub>M)"
proof (cases "t \<epsilon> x") 
  assume "\<not> t \<epsilon> x"
  show ?thesis
    unfolding dedekind_fin_def  
  proof (rule, rule)
    have IH: "u \<subset>\<^sub>M x \<Longrightarrow> x \<approx>\<^sub>M u \<Longrightarrow> False" for u
      using assms unfolding dedekind_fin_def  by blast
    show "\<not> x \<union>\<^sub>M {t}\<^sub>M \<approx>\<^sub>M y" if "y \<subset>\<^sub>M x \<union>\<^sub>M {t}\<^sub>M" for y
    proof
      assume "x \<union>\<^sub>M {t}\<^sub>M \<approx>\<^sub>M y"
      then obtain f where f_bij: "one_oneM f" and f_dom: "domM f = x \<union>\<^sub>M {t}\<^sub>M" and f_rng: "rngM f = y" 
        unfolding set_equivalent_def by force
      obtain ft where "\<langle>t,ft\<rangle> \<epsilon> f"
        using f_dom[unfolded setext dom_def', rule_format, of t] unfolding pow_setsuc_def' by force
          \<comment> \<open>From this we construct a bijection \<open>g\<close> between  strict subset \<open>y'\<close> of \<open>x\<close> and \<open>x\<close>
       There are two different constructions. Depending on whether removing the pair \<open>fx,x\<close> from \<open>f\<close> 
       yields directly a bijection of \<open>x\<close> on its subset, or whether a modification is needed. 
       \<close>
      have "ft \<epsilon> y"
        using \<open>rngM f = y\<close> \<open>\<langle>t,ft\<rangle> \<epsilon> f\<close> unfolding setext rng_def' by blast
      consider "t \<epsilon> y \<and> ft \<noteq> t" | "y \<subseteq>\<^sub>M x \<or> ft = t" 
        using \<open>y \<subset>\<^sub>M x \<union>\<^sub>M {t}\<^sub>M\<close> unfolding subsetM_def proper_subsetM_def pow_setsuc_def' by blast
      then show False
      proof (cases) 
        assume "y \<subseteq>\<^sub>M x \<or> ft = t" 
          \<comment> \<open>First construction just removes \<open>\<langle>t,ft\<rangle>\<close>\<close>
        obtain y' where y': "\<forall> u. u \<epsilon> y' \<longleftrightarrow> u \<epsilon> y \<and> u \<noteq> ft"
          using sep_sr[rule_format, of "(\<noteq>)"] unfolding SetRelation_def by force 
        obtain g where g: "\<forall> u. u \<epsilon> g \<longleftrightarrow> u \<epsilon> f \<and> u \<noteq> \<langle>t,ft\<rangle>"
          using sep_sr[rule_format, of "(\<noteq>)"] unfolding SetRelation_def by force 
        show False
        proof (rule IH)
          show "y' \<subset>\<^sub>M x"
            using y' \<open>y \<subseteq>\<^sub>M x \<or> ft = t\<close>[unfolded subsetM_def] \<open>ft \<epsilon> y\<close> proper_subsetM_def \<open>y \<subset>\<^sub>M x \<union>\<^sub>M {t}\<^sub>M\<close>[unfolded proper_subsetM_def pow_setsuc_def' setext[of y]] by metis 
          show "x \<approx>\<^sub>M y'"
          proof-  
            have "one_oneM g"
              using \<open>one_oneM f\<close> g unfolding one_oneM_def functionM_def relationM_def by blast
            have "domM g = x"
              using fun_inj[OF conjunct1[OF f_bij[unfolded one_oneM_def]] \<open>\<langle>t,ft\<rangle> \<epsilon> f\<close>] f_dom mem_not_refl \<open>\<not> t \<epsilon> x\<close>  
              unfolding setext[of "domM _"] dom_def' y'[rule_format] g[rule_format] one_oneM_def functionM_def pow_setsuc_def' ordered_pair_unique by blast
            have "rngM g = y'"
              using one_one_inj[OF f_bij \<open>\<langle>t,ft\<rangle> \<epsilon> f\<close>] f_rng 
              unfolding setext[of "rngM _"] rng_def' y'[rule_format] g[rule_format] ordered_pair_unique
              by blast
            show "x \<approx>\<^sub>M y'"
              unfolding set_equivalent_def using \<open>rngM g = y'\<close> \<open>domM g = x\<close> \<open>one_oneM g\<close>  by blast 
          qed
        qed
      next
        assume "t \<epsilon> y \<and> ft \<noteq> t"
        then obtain pt where "\<langle>pt,t\<rangle> \<epsilon> f"
          using f_rng[unfolded setext rng_def', rule_format, of t] by blast
        hence "pt \<epsilon> x"
          using f_dom[unfolded setext[of "domM _"] dom_def' pow_setsuc_def']
            one_oneD3[OF f_bij, rule_format, of t ft t] \<open>\<langle>pt,t\<rangle> \<epsilon> f\<close> \<open>\<langle>t,ft\<rangle> \<epsilon> f\<close> \<open>t \<epsilon> y \<and> ft \<noteq> t\<close> by blast  
        then show False
        proof- 
          \<comment> \<open>the second construction requires to modify the mapping \<open>f\<close> by adding \<open>\<langle>fx,px\<rangle>\<close>, not just to restrict \<open>f\<close>\<close>
          obtain y' where y': "\<forall> u. u \<epsilon> y' \<longleftrightarrow> u \<epsilon> y \<and> u \<noteq> t"
            using sep_sr[rule_format, of "(\<noteq>)"] unfolding SetRelation_def by force
          have sfp: "SetFormulaPredicate (\<lambda> \<Xi>. \<Xi> 0 = \<langle>\<Xi> 1,\<Xi> 2\<rangle> \<or> (\<Xi> 0 \<epsilon> \<Xi> 4 \<and> \<Xi> 0 \<noteq> \<langle>\<Xi> 3,\<Xi> 2\<rangle> \<and> \<Xi> 0 \<noteq> \<langle>\<Xi> 1,\<Xi> 3\<rangle>))"
            unfolding logsimps by rule+
          obtain g where g: "\<forall> u. u \<epsilon> g \<longleftrightarrow> (u = \<langle>pt,ft\<rangle> \<or> (u \<epsilon> f \<and> u \<noteq> \<langle>t,ft\<rangle> \<and> u \<noteq> \<langle>pt,t\<rangle>))"
            using sep[rule_format, OF sfp, of "f \<union>\<^sub>M {\<langle>pt,ft\<rangle>}\<^sub>M" "undefined(1:=pt, 2:=ft, 3:= t ,4:=f)", simplified] by auto           
          show False
          proof (rule IH)
            show "y' \<subset>\<^sub>M x"
              using \<open>y \<subset>\<^sub>M x \<union>\<^sub>M {t}\<^sub>M\<close> \<open>t \<epsilon> y \<and> ft \<noteq> t\<close> unfolding proper_subsetM_def y'[rule_format] pow_setsuc_def' setext[of y] setext[of y'] by blast
            show "x \<approx>\<^sub>M y'"
            proof-  
              have "one_oneM g"
                by (rule one_oneI, unfold g[rule_format] ordered_pair_unique) 
                (use one_oneD1[OF f_bij] in blast, 
                use one_oneD2[OF f_bij] \<open>\<langle>t,ft\<rangle> \<epsilon> f\<close> in blast,
                use one_oneD3[OF f_bij] \<open>\<langle>pt,t\<rangle> \<epsilon> f\<close> in blast) 
              have "domM g = x"
                unfolding setext[of "domM _"] dom_def' 
              proof (rule, rule)
                fix z assume "\<exists>v. \<langle>z,v\<rangle> \<epsilon> g" 
                show "z \<epsilon> x"
                  using \<open>\<exists>v. \<langle>z,v\<rangle> \<epsilon> g\<close> \<open>pt \<epsilon> x\<close>  one_oneD3[OF f_bij, rule_format, of t ft _] \<open>\<langle>t,ft\<rangle> \<epsilon> f\<close> f_dom[unfolded setext[of "domM _"] pow_setsuc_def' dom_def'] unfolding ordered_pair_unique 
                    g[rule_format] by blast
              next
                fix z assume " z \<epsilon> x" 
                then show "\<exists>v. \<langle>z,v\<rangle> \<epsilon> g"
                  unfolding g[rule_format] using mem_not_refl f_dom[unfolded setext[of "domM _"] pow_setsuc_def' dom_def'] by (cases "z = pt") (use \<open>\<not> t \<epsilon> x\<close> in auto) 
              qed
              have "rngM g = y'"
                unfolding setext[of "rngM _"] rng_def'
              proof (rule, rule)
                fix z assume "\<exists>v. \<langle>v,z\<rangle> \<epsilon> g"
                show "z \<epsilon> y'"
                  using 
                    one_oneD2[OF f_bij]
                   \<open>\<exists>v. \<langle>v,z\<rangle> \<epsilon> g\<close> \<open>ft \<epsilon> y\<close> \<open>t \<epsilon> y \<and> ft \<noteq> t\<close>  \<open>\<langle>pt,t\<rangle> \<epsilon> f\<close> \<open>\<langle>t,ft\<rangle> \<epsilon> f\<close>
                  unfolding f_rng[unfolded setext[of "rngM _"]  rng_def', rule_format, symmetric, of z]  y'[rule_format] ordered_pair_unique g[rule_format] by blast
              next
                fix z assume "z \<epsilon> y'"
                show "\<exists>v. \<langle>v,z\<rangle> \<epsilon> g"
                  using \<open>z \<epsilon> y'\<close>[unfolded y'[rule_format]]
                  unfolding f_rng[unfolded setext[of "rngM _"]  rng_def', rule_format, symmetric, of z] g[rule_format] ordered_pair_unique by blast
              qed
              show "x \<approx>\<^sub>M y'"
                unfolding set_equivalent_def using \<open>rngM g = y'\<close> \<open>domM g = x\<close> \<open>one_oneM g\<close>  by blast 
            qed
          qed
        qed
      qed
    qed
  qed
qed (simp add: assms)

lemma dedekind_finite_nat: assumes "natM x"  shows "dedekind_fin x"
  using nat_induction_sp[OF SP_dedekind empty_dedekind \<open>natM x\<close>] dedekind_finite_suc by blast

lemma nat_equiv_unique: assumes "natM x" "natM y" "x \<approx>\<^sub>M y"
  shows "x = y"
proof (rule ccontr)
  assume "x \<noteq> y"
  have "\<not> y \<epsilon> x"  
    using \<open>x \<noteq> y\<close> assms dedekind_finite_nat[unfolded dedekind_fin_def, rule_format, OF \<open>natM x\<close>] ordM_D1[OF natM_D1[OF \<open>natM x\<close>]] subsetM_def proper_subset_def' by blast 
  have "\<not> x \<epsilon> y"  
    using \<open>x \<noteq> y\<close> assms dedekind_finite_nat[unfolded dedekind_fin_def, rule_format, OF \<open>natM y\<close>] ordM_D1[OF natM_D1[OF \<open>natM y\<close>]] 
     subsetM_def proper_subset_def' set_equivalent_sym[of x y] by blast
  show False
    using \<open>\<not> x \<epsilon> y\<close> \<open>\<not> y \<epsilon> x\<close> \<open>x \<noteq> y\<close>  ordM_total[OF natM_D1 natM_D1, OF assms(1,2)] by blast
qed     

lemma card_inj: assumes "cardinality x n" "cardinality x m" shows "n = m"
  using assms unfolding cardinality_def  using nat_equiv_unique set_equivalent_sym set_equivalent_trans  by blast

sublocale L_setind
proof (unfold_locales, rule, rule, rule, rule ccontr)
  fix P \<Xi> x
  assume "SetFormulaPredicate P" "P (\<Xi> (0:= \<emptyset>))" and step:  "\<forall>x y. P (\<Xi> (0:= x)) \<longrightarrow> P ((\<Xi> (0:=x \<union>\<^sub>M {y}\<^sub>M)))" and "\<not> (P (\<Xi> (0:=x)))"
  have sfp: "SetFormulaPredicate (\<lambda> \<Xi>. cardinality (\<Xi> 0) (\<Xi> 1))"
    unfolding set_defs logsimps by rule+
  have cinj: "cardinality u v \<and> cardinality u w \<Longrightarrow> v = w" for u v w
    using card_inj by auto
  from sep[OF \<open>SetFormulaPredicate P\<close>, rule_format, of"\<PP> x" \<Xi>]
  obtain s where s: "\<forall>u. (u \<epsilon> s) = (u \<epsilon> \<PP> x \<and> P (\<Xi>(0 := u)))"
    by blast
  from replp_vars[rule_format, OF sfp, of \<Xi> 0 1 s, simplified] 
  obtain m where m: "\<forall>v. (v \<epsilon> m) = (\<exists>a. a \<epsilon> s \<and> cardinality a v) " 
    using cinj by blast
  have "\<emptyset> \<epsilon> m"
    using card_emp exI[of "\<lambda> x. x \<subseteq>\<^sub>M c \<and> P (\<Xi> (0:=x, 1:=\<emptyset>)) \<and> cardinality x \<emptyset>" \<emptyset>] \<open>P (\<Xi> (0:=\<emptyset>))\<close> 
    unfolding m[rule_format] powerset_def' subsetM_def s[rule_format]
    using empty_set_def'  by auto 
  have "n \<union>\<^sub>M {n}\<^sub>M \<epsilon> m" if "n \<epsilon> m" for n
  proof-                  
    obtain y where "y \<epsilon> \<PP> x" "cardinality y n" "P (\<Xi> (0:=y))"
      using m  \<open>n \<epsilon> m\<close> s by fast
    obtain y' where "y' \<epsilon> x" "\<not> y' \<epsilon> y" 
      using \<open>y \<epsilon> \<PP> x\<close> \<open>P (\<Xi> (0:=y))\<close> \<open>\<not> P (\<Xi> (0:=x))\<close> subsetM_antisym powerset_def' subsetM_def by blast
    show "n \<union>\<^sub>M {n}\<^sub>M \<epsilon> m"
      unfolding m[rule_format] 
    proof (rule exI[of _ "y \<union>\<^sub>M {y'}\<^sub>M"])  
      show "y \<union>\<^sub>M {y'}\<^sub>M \<epsilon> s \<and> cardinality (y \<union>\<^sub>M {y'}\<^sub>M) (n \<union>\<^sub>M {n}\<^sub>M)"
        using card_suc[OF \<open>\<not> y' \<epsilon> y\<close> \<open>cardinality y n\<close>] \<open>y \<epsilon> \<PP> x\<close> \<open>y' \<epsilon> x\<close>  
          step[rule_format, OF \<open>P (\<Xi>(0:= y))\<close>] unfolding powerset_def' subsetM_def s[rule_format] by simp
    qed 
  qed
  then show False
    using fin \<open>\<emptyset> \<epsilon> m\<close> by blast
qed

lemma cardinality_ex: "\<exists>! n. natM n \<and> x \<approx>\<^sub>M n"
proof (rule ex_ex1I)
  show "\<exists> n. natM n \<and> x \<approx>\<^sub>M n"
  proof (rule setind_SP[rule_format])
    show "SetProperty (\<lambda>a. \<exists>n. natM n \<and> a \<approx>\<^sub>M n)"
      unfolding SetProperty_def set_defs logsimps by rule+
    show "\<exists>n. natM n \<and> \<emptyset> \<approx>\<^sub>M n"
      using card_emp cardinality_def by blast
    show "\<exists>n. natM n \<and> x \<union>\<^sub>M {y}\<^sub>M \<approx>\<^sub>M n" if "\<exists>n. natM n \<and> x \<approx>\<^sub>M n" for x y
      using that card_suc triv_suc unfolding cardinality_def  by metis 
  qed
  show "natM n \<and> x \<approx>\<^sub>M n \<Longrightarrow> natM y \<and> x \<approx>\<^sub>M y \<Longrightarrow> n = y" for n x y
    using nat_equiv_unique set_equivalent_sym set_equivalent_trans by blast
qed

lemma dedekind_finite: "\<forall> x. dedekind_fin x"
  using setind_SP[rule_format, OF SP_dedekind empty_dedekind] dedekind_finite_suc by blast

sublocale L_dedekind
  using dedekind_finite by unfold_locales  

sublocale L_tarski
  by unfold_locales (use empty_tarski set_signature.SP_tarski setind_SP tarski_suc_tarski in blast)


lemma ord_iff_nat: "ordM x \<longleftrightarrow> natM x"
  unfolding ordM_def natM_def using tarski by blast 

text \<open>The following theorem corresponds to Theorem 4.2 in Kaye-Wong\<close>

lemma nat_iff_suc: "natM x \<longleftrightarrow> x = \<emptyset> \<or> (\<exists> y. natM y \<and> x = y \<union>\<^sub>M {y}\<^sub>M)"
proof 
  show "x = \<emptyset> \<or> (\<exists>y. natM y \<and> x = y \<union>\<^sub>M {y}\<^sub>M) \<Longrightarrow> natM x"
    using emp_natM nat_suc_nat by blast
next
  fix x assume "natM x"
  have "SetProperty (\<lambda>a. a = \<emptyset> \<or> (\<exists>y. natM y \<and> a = y \<union>\<^sub>M {y}\<^sub>M))"
    unfolding SetProperty_def set_defs logsimps setext by rule+ 
  show "x = \<emptyset> \<or> (\<exists>y. natM y \<and> x = y \<union>\<^sub>M {y}\<^sub>M)"
    by (rule nat_induction_sp, fact, simp, fact, blast) 
qed

end

subsection \<open>Dedekind finite\<close>

locale L_setext_empty_power_union_repl_dedekind = L_setext + L_dedekind + L_empty + L_power + L_union + L_repl

begin

sublocale L_setext_empty_repl
  by unfold_locales

sublocale L_setext_empty_power_union_repl
  by unfold_locales  

lemma neg_inf: "\<nexists> x. \<emptyset> \<epsilon> x \<and> (\<forall>y. y \<epsilon> x \<longrightarrow> y \<union>\<^sub>M {y}\<^sub>M \<epsilon> x)"
proof
  assume "\<exists>x. \<emptyset> \<epsilon> x \<and> (\<forall>y. y \<epsilon> x \<longrightarrow> y \<union>\<^sub>M {y}\<^sub>M \<epsilon> x)"
  then obtain x' where x': "\<emptyset> \<epsilon> x'" "\<forall>y. y \<epsilon> x' \<longrightarrow> y \<union>\<^sub>M {y}\<^sub>M \<epsilon> x'"
    by blast
  define x where "x = separationM x' natM"
  from separ_def_sp[OF SP_nat]
  have x: "u \<epsilon> x \<longleftrightarrow> u \<epsilon> x' \<and> natM u" for u
    unfolding x_def. 
  have x_suc: "u \<epsilon> x \<longrightarrow> u \<union>\<^sub>M {u}\<^sub>M \<epsilon> x" for u
    using x'(2) nat_suc_nat[of u] unfolding x by blast 
  have "SetFormulaPredicate (\<lambda> \<Xi>. \<exists> v. \<Xi> 0 = \<langle>v,v \<union>\<^sub>M {v}\<^sub>M\<rangle>)"
    unfolding logsimps set_defs by rule+ 
  from sep[OF this, rule_format, of "x \<times>\<^sub>M x", simplified]
  obtain f where "u \<epsilon> f \<longleftrightarrow> (u \<epsilon> x \<times>\<^sub>M x  \<and> (\<exists>v. u = \<langle>v,v \<union>\<^sub>M {v}\<^sub>M\<rangle>))" for u
    by blast
  hence f: "u \<epsilon> f \<longleftrightarrow> (\<exists> v. v \<epsilon> x \<and> u = \<langle>v,v \<union>\<^sub>M {v}\<^sub>M\<rangle>)" for u
    using car_prod_def' x_suc by auto
  have "one_oneM f"
    by (rule one_oneI, unfold f x, blast, unfold ordered_pair_unique)  
      (use ord_pred_inj[OF natM_D1 natM_D1] in blast)+
  have "domM f = x"
    unfolding setext[of _ x] f dom_def' by force 
  have "x \<approx>\<^sub>M rngM f"
    unfolding set_equivalent_def by (rule exI[of _ f]) (use \<open>one_oneM f\<close> \<open>domM f = x\<close> in blast)
  have "rngM f \<subset>\<^sub>M x"
  proof (rule proper_subsetI)
    show "rngM f \<subseteq>\<^sub>M x"
      unfolding subsetM_def rng_def' f ordered_pair_unique using x_suc by blast
    show "rngM f \<noteq> x"
      unfolding setext[of _ x] rng_def' not_all
    proof (rule exI[of _ \<emptyset>])
      have t: "\<emptyset> \<epsilon> x = True"
        by (simp add: x x'(1))
      have f: "(\<exists> v. \<langle>v,\<emptyset>\<rangle> \<epsilon> f) = False"
        unfolding f ordered_pair_unique setext[of \<emptyset>] binunion_def' singleton_def' by force
      show "(\<exists>v. \<langle>v,\<emptyset>\<rangle> \<epsilon> f) \<noteq> (\<emptyset> \<epsilon> x)"
        unfolding t f by blast
    qed
  qed
  from dedekind[unfolded dedekind_fin_def, rule_format, OF this] 
  show False
    using \<open>x \<approx>\<^sub>M rngM f\<close> by blast
qed

sublocale L_fin
  using neg_inf by unfold_locales

end

subsection \<open>Successor induction\<close> 
text \<open>See P. Vopěnka, Mathematics in the alternative set theory. Teubner 1979\<close>

locale L_setext_empty_setsuc_setind = L_setext + L_empty + L_setsuc + L_setind 

begin

sublocale L_setext_empty_setsuc
  by unfold_locales

sublocale L_setext_pair
  by unfold_locales (metis empty setsuc)

lemma binunion_ex:
  shows "\<exists> z. (\<forall> u. u \<epsilon> z \<longleftrightarrow> u \<epsilon> x \<or> u \<epsilon> x')" (is "?P x x'")
proof-
  have SR: "SetRelation ?P"
    unfolding SetRelation_def logsimps by rule+ 
  show ?thesis
  proof (rule  setind[rule_format, OF  SR[unfolded SetRelation_def], of "undefined(0:=x,1:=x')", simplified], force)
    fix x y :: 'a
    assume ex: "\<exists>z. \<forall>u. (u \<epsilon> z) \<longleftrightarrow> (u \<epsilon> x \<or> u \<epsilon> x')"
    then show "\<exists>z. \<forall>u. (u \<epsilon> z) \<longleftrightarrow> (u \<epsilon> (x\<union>\<^sub>M{y}\<^sub>M) \<or> u \<epsilon> x')"
      unfolding setsuc_def' using setsuc[rule_format, of _ y]  by metis
  qed  
qed

sublocale L_union
proof (unfold_locales, rule, rule setind_SP[rule_format])
  show "\<exists>z. \<forall>u. (u \<epsilon> z) \<longleftrightarrow> (\<exists>v. v \<epsilon> \<emptyset> \<and> u \<epsilon> v)"
    by (meson empty_is_empty)
next 
  fix x y
  have aux: "(\<forall>u. (u \<epsilon> z) \<longleftrightarrow> (\<exists>v. (v \<epsilon> x \<or> v = y) \<and> u \<epsilon> v)) \<longleftrightarrow> (\<forall>u. (u \<epsilon> z) \<longleftrightarrow> (\<exists> v. v \<epsilon> x \<and> u \<epsilon> v) \<or> u \<epsilon> y)" for z
    by blast
  let ?Q = "\<lambda> z. \<forall>u. (u \<epsilon> z) = (\<exists>v. (v \<epsilon> x \<or> v = y) \<and> u \<epsilon> v)"
  assume "\<exists>z. \<forall>u. (u \<epsilon> z) \<longleftrightarrow> (\<exists>v. v \<epsilon> x \<and> u \<epsilon> v)"
  thus "\<exists>z. \<forall>u. (u \<epsilon> z) \<longleftrightarrow> (\<exists>v. v \<epsilon> (x\<union>\<^sub>M{y}\<^sub>M) \<and> u \<epsilon> v)"
    unfolding setsuc_def' aux using binunion_ex[rule_format, of _ y] by metis
next
  show "SetProperty (\<lambda>a. \<exists>z. \<forall>u. (u \<epsilon> z) = (\<exists>v. v \<epsilon> a \<and> u \<epsilon> v))"
    unfolding SetProperty_def logsimps by rule+
qed

sublocale L_repl
proof (unfold_locales, rule, rule)
  fix P x \<Xi> 
  assume "SetFormulaPredicate P" and func: "\<forall>u. \<exists>!v. P (\<Xi>(0 := u, 1 := v))"
  from bounded_free[OF \<open>SetFormulaPredicate P\<close>]
  obtain m where m: "\<forall> \<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow>  P \<Xi> = P \<Xi>'"
    by blast
  hence small: "P (\<Xi>(m := x, 0 := u, 1 := v)) = P (\<Xi>(0 := u, 1 := v))" for u v x
    by simp
  let ?P = "\<lambda>\<Xi>. \<exists>z. \<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> \<Xi> m \<and> P (\<Xi> (0:=u,1:=v)))"
  have sfp: "SetFormulaPredicate ?P"
    by (rule SFP_replace) fact+  
  note aux_rule = setind_var[rule_format, of ?P \<Xi> m x, OF sfp, unfolded small, simplified, unfolded One_nat_def[symmetric]] 
  show "\<exists>z. \<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> x \<and> P (\<Xi>(0 := u, 1 := v)))"
  proof (rule aux_rule)
    fix x y
    assume "\<exists>z. \<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> x \<and> P (\<Xi>(0 := u, 1 := v)))"
    then obtain z where z: "\<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> x \<and> P (\<Xi>(0 := u, 1 := v)))"
      by blast
    obtain y' where y': "P (\<Xi>(0 := y, 1 := y'))"
      using func by blast
    show "\<exists>z. \<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> x \<union>\<^sub>M {y}\<^sub>M \<and> P (\<Xi>(0 := u, 1 := v)))"
      by (rule exI[of "\<lambda> z. \<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> x \<union>\<^sub>M {y}\<^sub>M \<and> P (\<Xi>(0 := u, 1 := v)))" "z \<union>\<^sub>M {y'}\<^sub>M"])
      (unfold setsuc_def', use y' z func in blast)
  qed (simp only: empty)
qed

sublocale L_setext_empty_repl
  by unfold_locales

lemma suc_separ: assumes "y \<epsilon> u" 
  shows "u = separationM u (\<lambda> x. x \<noteq> y) \<union>\<^sub>M {y}\<^sub>M"
proof-
  have sfp: "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> 0 \<noteq> \<Xi> 1)"
    by rule+
  show ?thesis 
    unfolding setext[of u] setsuc_def' separ_def_sr[of "(\<noteq>)" _ u y, unfolded SetRelation_def, OF sfp] using \<open>y \<epsilon> u\<close> by blast
qed

lemma suc_subset_setind: "u \<subseteq>\<^sub>M x \<union>\<^sub>M {y}\<^sub>M \<longleftrightarrow> u \<subseteq>\<^sub>M x \<or> (\<exists> u'. u' \<subseteq>\<^sub>M x \<and> u = u' \<union>\<^sub>M {y}\<^sub>M)"
proof
  assume "u \<subseteq>\<^sub>M x \<union>\<^sub>M {y}\<^sub>M"
  show "u \<subseteq>\<^sub>M x \<or> (\<exists>u'. u' \<subseteq>\<^sub>M x \<and> u = u' \<union>\<^sub>M {y}\<^sub>M)"
  proof (unfold disj_imp, rule impI)   
    assume "\<not> u \<subseteq>\<^sub>M x"
    hence "y \<epsilon> u"
      using \<open>u \<subseteq>\<^sub>M x \<union>\<^sub>M {y}\<^sub>M\<close> subsetM_def setsuc_def' by auto 
    have "separationM u (\<lambda> x. x \<noteq> y)  \<subseteq>\<^sub>M x"
      using \<open>u \<subseteq>\<^sub>M x \<union>\<^sub>M {y}\<^sub>M\<close> unfolding subsetM_def
      separ_def_sr[of "(\<noteq>)", unfolded SetRelation_def, OF SFP_neg[OF SFP_eq]] setsuc_def' by blast
    with suc_separ[OF \<open>y \<epsilon> u\<close>]
    show "\<exists>u'. u' \<subseteq>\<^sub>M x \<and> u = u' \<union>\<^sub>M {y}\<^sub>M"
      by blast
  qed
next
  assume "u \<subseteq>\<^sub>M x \<or> (\<exists>u'. u' \<subseteq>\<^sub>M x \<and> u = u' \<union>\<^sub>M {y}\<^sub>M)"
  then show "u \<subseteq>\<^sub>M x \<union>\<^sub>M {y}\<^sub>M "
  proof
    show "u \<subseteq>\<^sub>M x \<Longrightarrow> u \<subseteq>\<^sub>M x \<union>\<^sub>M {y}\<^sub>M"
      unfolding subsetM_def setsuc_def' by blast
    assume "\<exists>u'. u' \<subseteq>\<^sub>M x \<and> u = u' \<union>\<^sub>M {y}\<^sub>M"
    then show "u \<subseteq>\<^sub>M x \<union>\<^sub>M {y}\<^sub>M"
      unfolding subsetM_def setext[of u] setsuc_def' by blast
  qed
qed
        
sublocale L_power
proof (unfold_locales, rule)
  fix x
  show "\<exists>y. \<forall>u. (u \<epsilon> y) = u \<subseteq>\<^sub>M x"
  thm setind_SP[of "\<lambda> x. \<exists>y. \<forall>u. (u \<epsilon> y) = u \<subseteq>\<^sub>M x"]
proof (rule setind_SP[rule_format])
  show "SetProperty (\<lambda>a. \<exists>y. \<forall>u. (u \<epsilon> y) = u \<subseteq>\<^sub>M a)"
    unfolding SetProperty_def logsimps set_defs by rule+
  show "\<exists>y. \<forall>u. (u \<epsilon> y) = u \<subseteq>\<^sub>M \<emptyset>"
    using setsuc_singletonM_ex[of \<emptyset>] by simp 
    fix x y 
    let ?P = "\<lambda> \<Xi>. \<Xi> 1 = \<Xi> 0 \<union>\<^sub>M {\<Xi> 2}\<^sub>M"
    have sfp: "SetFormulaPredicate ?P"
      unfolding setext logsimps set_defs by rule+
    have ex1: "\<exists>! v. v = u \<union>\<^sub>M {y}\<^sub>M" for u
      by blast 
    have  binunion_def': "u \<epsilon> x \<union>\<^sub>M y \<longleftrightarrow> u \<epsilon> x \<or> u \<epsilon> y" for u x y
       using collect_def_ex[OF binunion_ex[rule_format, of x y], folded binunionM_def].
    assume "\<exists>z. \<forall>u. (u \<epsilon> z) = u \<subseteq>\<^sub>M x"
    then obtain z where z: "\<forall>u. (u \<epsilon> z) = u \<subseteq>\<^sub>M x"
      by blast
    obtain z' where z': "\<forall> v. v \<epsilon> z' \<longleftrightarrow> (\<exists> u. u \<epsilon> z \<and> v = u \<union>\<^sub>M {y}\<^sub>M)"
      using replf[OF sfp, of "undefined(2:=y)",  simplified] by blast
    show "\<exists>z. \<forall>u. (u \<epsilon> z) = u \<subseteq>\<^sub>M x \<union>\<^sub>M {y}\<^sub>M"
      by (rule exI[of "\<lambda> z.(\<forall>u. (u \<epsilon> z) = u \<subseteq>\<^sub>M x \<union>\<^sub>M {y}\<^sub>M)" "z \<union>\<^sub>M z'"])
        (unfold binunion_def' suc_subset_setind, use z z' in simp)
  qed 
qed

sublocale L_setext_empty_power_union_repl
  by unfold_locales

lemma min_subset_ex: assumes "u \<noteq> \<emptyset>" shows "\<exists> z. z \<epsilon> u \<and> (\<nexists> w. w \<epsilon> u \<and> w \<subset>\<^sub>M z)"
proof (rule mp[OF _ assms], rule setind_SP[rule_format])
  show "SetProperty (\<lambda>a. a \<noteq> \<emptyset> \<longrightarrow> (\<exists>z. z \<epsilon> a \<and> (\<nexists>w. w \<epsilon> a \<and> w \<subset>\<^sub>M z)))"
    unfolding SetProperty_def set_defs logsimps by rule+
next
  fix  x y
  assume IH: "x \<noteq> \<emptyset> \<longrightarrow> (\<exists>z. z \<epsilon> x \<and> (\<nexists>w. w \<epsilon> x \<and> w \<subset>\<^sub>M z))"
  show "x \<union>\<^sub>M {y}\<^sub>M \<noteq> \<emptyset> \<longrightarrow> (\<exists>z. z \<epsilon> x \<union>\<^sub>M {y}\<^sub>M \<and> (\<nexists>w. w \<epsilon> x \<union>\<^sub>M {y}\<^sub>M \<and> w \<subset>\<^sub>M z))" 
  proof (rule, cases "x = \<emptyset>")
    assume "x = \<emptyset>"
    then show "\<exists>z. z \<epsilon> x \<union>\<^sub>M {y}\<^sub>M \<and> (\<nexists>w. w \<epsilon> x \<union>\<^sub>M {y}\<^sub>M \<and> w \<subset>\<^sub>M z)"
      using singleton_def' by force
  next
    assume "x \<noteq> \<emptyset>"
    from IH[rule_format, OF this]
    obtain u where "u \<epsilon> x" and nex: "\<nexists>w. w \<epsilon> x \<and> w \<subset>\<^sub>M u"
      by blast
    show "\<exists>z. z \<epsilon> x \<union>\<^sub>M {y}\<^sub>M \<and> (\<nexists>w. w \<epsilon> x \<union>\<^sub>M {y}\<^sub>M \<and> w \<subset>\<^sub>M z)"
    proof (cases "y \<subset>\<^sub>M u")
      assume "y \<subset>\<^sub>M u"
      have "y \<epsilon> x \<union>\<^sub>M {y}\<^sub>M"
        using setsuc_def' by auto
      show ?thesis
      proof (rule exI[of _ y], rule conjI[OF \<open>y \<epsilon> x \<union>\<^sub>M {y}\<^sub>M\<close>], rule notI)
        assume "\<exists>w. w \<epsilon> x \<union>\<^sub>M {y}\<^sub>M \<and> w \<subset>\<^sub>M y"
        then show False
          using \<open>y \<subset>\<^sub>M u\<close> \<open>y \<epsilon> x \<union>\<^sub>M {y}\<^sub>M\<close> nex proper_subsetM_trans[OF _ \<open>y \<subset>\<^sub>M u\<close>]
          by (metis proper_subsetM_def setsuc_def') 
      qed
    next
      assume "\<not> y \<subset>\<^sub>M u"
      show ?thesis
        by (rule exI[of _ u]) (use setsuc_def' \<open>u \<epsilon> x\<close> nex \<open>\<not> y \<subset>\<^sub>M u\<close> in metis)
    qed
  qed
qed simp

text \<open>A stronger version of Tarski finiteness axiom:  not only subsets of a powersets have maximal element w.r.t. subset relation but all sets have such a maximum.   This is clearly equivalent to the Tarski finiteness axiom if every set is a subset of some powerset. Since each set is a subset of the powerset of its union, we have this equivalence if union exists.\<close>

lemma max_subset_ex: assumes "u \<noteq> \<emptyset>" shows "\<exists> z. z \<epsilon> u \<and> (\<nexists> w. w \<epsilon> u \<and> z \<subset>\<^sub>M w)"
proof (rule mp[OF _ assms], rule setind_SP[rule_format])
  show "SetProperty (\<lambda>a. a \<noteq> \<emptyset> \<longrightarrow> (\<exists>z. z \<epsilon> a \<and> (\<nexists>w. w \<epsilon> a \<and> z \<subset>\<^sub>M w)))"
    unfolding SetProperty_def set_defs logsimps by rule+
next
  fix  x y
  assume IH: "x \<noteq> \<emptyset> \<longrightarrow> (\<exists>z. z \<epsilon> x \<and> (\<nexists>w. w \<epsilon> x \<and> z \<subset>\<^sub>M w))"
  show "x \<union>\<^sub>M {y}\<^sub>M \<noteq> \<emptyset> \<longrightarrow> (\<exists>z. z \<epsilon> x \<union>\<^sub>M {y}\<^sub>M \<and> (\<nexists>w. w \<epsilon> x \<union>\<^sub>M {y}\<^sub>M \<and> z \<subset>\<^sub>M w))" 
  proof (rule, cases "x = \<emptyset>")
    assume "x = \<emptyset>"
    then show "\<exists>z. z \<epsilon> x \<union>\<^sub>M {y}\<^sub>M \<and> (\<nexists>w. w \<epsilon> x \<union>\<^sub>M {y}\<^sub>M \<and> z \<subset>\<^sub>M w)"
      using singleton_def' by force
  next
    assume "x \<noteq> \<emptyset>"
    from IH[rule_format, OF this]
    obtain u where "u \<epsilon> x" and nex: "\<nexists>w. w \<epsilon> x \<and> u \<subset>\<^sub>M w"
      by blast
    show "\<exists>z. z \<epsilon> x \<union>\<^sub>M {y}\<^sub>M \<and> (\<nexists>w. w \<epsilon> x \<union>\<^sub>M {y}\<^sub>M \<and> z \<subset>\<^sub>M w)"
    proof (cases "u \<subset>\<^sub>M y")
      assume "u \<subset>\<^sub>M y"
      have "y \<epsilon> x \<union>\<^sub>M {y}\<^sub>M"
        using setsuc_def' by auto
      show ?thesis
      proof (rule exI[of _ y], rule conjI[OF \<open>y \<epsilon> x \<union>\<^sub>M {y}\<^sub>M\<close>], rule notI)
        assume "\<exists>w. w \<epsilon> x \<union>\<^sub>M {y}\<^sub>M \<and> y \<subset>\<^sub>M w"
        then show False
          using \<open>u \<subset>\<^sub>M y\<close> \<open>y \<epsilon> x \<union>\<^sub>M {y}\<^sub>M\<close> nex proper_subsetM_trans[OF _ \<open>u \<subset>\<^sub>M y\<close>]
          by (metis proper_subsetM_def setsuc_def')
      qed
    next
      assume "\<not> u \<subset>\<^sub>M y"
      show ?thesis
        by (rule exI[of _ u]) (use setsuc_def' \<open>u \<epsilon> x\<close> nex \<open>\<not> u \<subset>\<^sub>M y\<close> in metis)
    qed
  qed
qed simp

sublocale L_tarski
  using max_subset_ex 
  by unfold_locales (simp add: tarski_fin_def, metis empty)  

sublocale L_dedekind
proof (unfold_locales, unfold dedekind_fin_def, rule)
  fix x
  let ?Q = "\<lambda> x. \<not> (\<exists> u. u \<subset>\<^sub>M x \<and> u \<approx>\<^sub>M x)"
  have sp: "SetProperty ?Q"
    unfolding SetProperty_def logsimps set_defs by rule+
  have "\<nexists>u. u \<subset>\<^sub>M x \<and> u \<approx>\<^sub>M x" \<comment>\<open>by induction on \<open>?Q\<close>\<close>
  proof(rule setind_SP[OF sp], use empty_is_empty proper_subset_diff in blast, rule, rule, rule, rule)
    fix x y
    assume "\<nexists>u. u \<subset>\<^sub>M x \<and> u \<approx>\<^sub>M x" and contr: "\<exists>u. u \<subset>\<^sub>M x \<union>\<^sub>M {y}\<^sub>M \<and> u \<approx>\<^sub>M x \<union>\<^sub>M {y}\<^sub>M"
    then have "\<not> y \<epsilon> x"
      by force
    from contr 
    obtain u f where u: "u \<subset>\<^sub>M x \<union>\<^sub>M {y}\<^sub>M" and f: "one_oneM f" "x \<union>\<^sub>M {y}\<^sub>M = domM f" "u = rngM f"  
      unfolding set_equivalent_sym[of _ "_ \<union>\<^sub>M _"] unfolding set_equivalent_def  by blast
    obtain fy where "\<langle>y,fy\<rangle> \<epsilon> f" and "fy \<epsilon> u"
      using f by (metis dom_def' rng_def' setsuc_def')
    show False
    proof (cases "u \<subseteq>\<^sub>M x")
      assume "u \<subseteq>\<^sub>M x"
      let ?u' = "separationM u (\<lambda> v. v \<noteq> fy)"
      have u': "z \<epsilon> ?u' \<longleftrightarrow> z \<epsilon> u \<and> z \<noteq> fy" for z
        using separ_def_sfp[of "\<lambda> \<Xi>. \<Xi> 0 \<noteq> \<Xi> 1" z u "undefined(1:=fy)" 0, simplified].
      hence "?u' \<subset>\<^sub>M x"
        using u' \<open>u \<subseteq>\<^sub>M x\<close> \<open>fy \<epsilon> u\<close> unfolding proper_subsetM_def subsetM_def by blast
      let ?f' = "separationM f (\<lambda> v. v \<noteq> \<langle>y,fy\<rangle>)"
      have f': "a \<epsilon> ?f' \<longleftrightarrow> a \<epsilon> f \<and> a \<noteq> \<langle>y,fy\<rangle>" for a
        using separ_def_sfp[of "\<lambda> \<Xi>. \<Xi> 0 \<noteq> \<Xi> 1" a f "undefined(1:= \<langle>y,fy\<rangle>)" 0, simplified].
      have "one_oneM ?f'"
        by (rule one_oneI, unfold f',
            use one_oneD1[OF \<open>one_oneM f\<close>] in blast,
            use one_oneD2[OF \<open>one_oneM f\<close>] in blast,
            use one_oneD3[OF \<open>one_oneM f\<close>] in blast)
      have "x = domM ?f'"
        using f(2) \<open>\<langle>y,fy\<rangle> \<epsilon> f\<close> one_oneD3[OF f(1)] \<open>\<not> y \<epsilon> x\<close> unfolding setext[of _ "domM _"] u' dom_def' f' setsuc_def'
        by auto        
      have "?u' = rngM ?f'"
        using f(3) \<open>\<langle>y,fy\<rangle> \<epsilon> f\<close> one_one_inj[OF f(1)] unfolding setext[of _ "rngM _"] u' rng_def' f' 
        by auto  
      have "?u' \<approx>\<^sub>M x"
        unfolding set_equivalent_sym[of _ x] unfolding set_equivalent_def   
        by (rule exI[of _ ?f'] , simp add: \<open>one_oneM ?f'\<close> \<open>?u' = rngM ?f'\<close> \<open>x = domM ?f'\<close>)  
      thus False
        using \<open>\<nexists>u. u \<subset>\<^sub>M x \<and> u \<approx>\<^sub>M x\<close> \<open>?u' \<subset>\<^sub>M x\<close> by blast 
    next 
      assume "\<not> u \<subseteq>\<^sub>M x"  
      hence "y \<epsilon> u"
        using u(1)[unfolded proper_subset_def'] using setsuc_def' suc_subset_setind  by metis
      then obtain z where "\<langle>z,y\<rangle> \<epsilon> f"
        using f(3) rng_def' by blast
      show False
      proof (cases "z = y")
        assume "z = y"
        have "z = fy"
          using \<open>\<langle>y,fy\<rangle> \<epsilon> f\<close> \<open>\<langle>z,y\<rangle> \<epsilon> f\<close> \<open>z = y\<close> f(1) one_oneD3 by auto
        let ?u' = "separationM u (\<lambda> v. v \<noteq> fy)"
        have u': "z \<epsilon> ?u' \<longleftrightarrow> z \<epsilon> u \<and> z \<noteq> fy" for z
          using separ_def_sfp[of "\<lambda> \<Xi>. \<Xi> 0 \<noteq> \<Xi> 1" z u "undefined(1:=fy)" 0, simplified].
        have "?u' \<subset>\<^sub>M x"
          using u \<open>z = y\<close> \<open>z = fy\<close> \<open>fy \<epsilon> u\<close> unfolding setext[of u] setext[of _ x]  proper_subsetM_def u' setsuc_def' 
          by auto
        let ?f' = "separationM f (\<lambda> v. v \<noteq> \<langle>y,y\<rangle>)"
        have f': "a \<epsilon> ?f' \<longleftrightarrow> a \<epsilon> f \<and> a \<noteq> \<langle>y,y\<rangle>" for a
          using separ_def_sfp[of "\<lambda> \<Xi>. \<Xi> 0 \<noteq> \<Xi> 1" a f "undefined(1:= \<langle>y,y\<rangle>)" 0, simplified].
        have "one_oneM ?f'"
          by (rule one_oneI, unfold f',
              use one_oneD1[OF \<open>one_oneM f\<close>] in blast,
              use one_oneD2[OF \<open>one_oneM f\<close>] in blast,
              use one_oneD3[OF \<open>one_oneM f\<close>] in blast)
        have "x = domM ?f'"
          using f(2) \<open>\<langle>z,y\<rangle> \<epsilon> f\<close>[unfolded \<open>z = y\<close>] one_oneD3[OF f(1)] \<open>\<not> y \<epsilon> x\<close> 
          unfolding setext[of _ "domM _"] dom_def' f' setsuc_def' by auto
        have "?u' = rngM ?f'"
          using f(3) \<open>\<langle>y,fy\<rangle> \<epsilon> f\<close> \<open>z = fy\<close> \<open>z = y\<close>  one_one_inj[OF f(1)] unfolding setext[of _ "rngM _"] u' rng_def' f'
          by auto 
        have "?u' \<approx>\<^sub>M x"
          unfolding set_equivalent_sym[of _ x] unfolding set_equivalent_def   
          by (rule exI[of _ ?f'] , simp add: \<open>one_oneM ?f'\<close> \<open>?u' = rngM ?f'\<close> \<open>x = domM ?f'\<close>)  
        thus False
          using \<open>\<nexists>u. u \<subset>\<^sub>M x \<and> u \<approx>\<^sub>M x\<close> \<open>?u' \<subset>\<^sub>M x\<close> by blast 
      next
        assume "z \<noteq> y"
        let ?u' = "x \<inter>\<^sub>M u"
        have "?u' \<subset>\<^sub>M x" 
          using \<open>y \<epsilon> u\<close> \<open>\<not> y \<epsilon> x\<close> \<open>u \<subset>\<^sub>M x \<union>\<^sub>M {y}\<^sub>M\<close> 
          unfolding setsuc_def' proper_subsetM_def intersection_def'  setext[of u] setext[of _ x] by blast 
        let ?Q = "\<lambda> v. v \<epsilon> f \<and> v \<noteq> \<langle>z,y\<rangle> \<and> v \<noteq> \<langle>y,fy\<rangle> \<or> v = \<langle>z,fy\<rangle>"
        have sfp: "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> 0 \<noteq> \<Xi> 1 \<and> \<Xi> 0 \<noteq> \<Xi> 2)"
          unfolding logsimps by rule+
        let ?g' =  "collectM ?Q"
        have g': "a \<epsilon> ?g' \<longleftrightarrow> ?Q a" for a
          using collect_def'[of "separationM f (\<lambda>x. x \<noteq> \<langle>z,y\<rangle> \<and> x \<noteq> \<langle>y,fy\<rangle>) \<union>\<^sub>M {\<langle>z,fy\<rangle>}\<^sub>M" ?Q, unfolded setext[of "collectM _ "], rule_format, of a]
          unfolding setsuc_def' separ_def_sfp[of "\<lambda> \<Xi>. \<Xi> 0 \<noteq> \<Xi> 1 \<and> \<Xi> 0 \<noteq> \<Xi> 2" _ f "undefined(1:= \<langle>z,y\<rangle>,2:= \<langle>y,fy\<rangle>)" 0, OF sfp, simplified] by fast 
        have "one_oneM ?g'"
          by (rule one_oneI, unfold g', 
              use one_oneD1[OF f(1)] in blast,
              use one_oneD3[OF \<open>one_oneM f\<close>] \<open>\<langle>y,fy\<rangle> \<epsilon> f\<close>
              one_one_inj[OF f(1)] ordered_pair_unique in metis,
              use one_oneD3[OF \<open>one_oneM f\<close>] \<open>\<langle>z,y\<rangle> \<epsilon> f\<close> in fastforce)
        have "?u' = rngM ?g'"
          unfolding setext[of _ "rngM _"] rng_def' g' intersection_def'
        proof(rule, rule)
          fix t assume "t \<epsilon> x \<and> t \<epsilon> u"
          then show "\<exists>v. \<langle>v,t\<rangle> \<epsilon> f \<and> \<langle>v,t\<rangle> \<noteq> \<langle>z,y\<rangle> \<and> \<langle>v,t\<rangle> \<noteq> \<langle>y,fy\<rangle> \<or> \<langle>v,t\<rangle> = \<langle>z,fy\<rangle>"
            using \<open>\<not> y \<epsilon> x\<close> f(3) rng_def' by auto
        next
          fix t assume a: "\<exists>v. \<langle>v,t\<rangle> \<epsilon> f \<and> \<langle>v,t\<rangle> \<noteq> \<langle>z,y\<rangle> \<and> \<langle>v,t\<rangle> \<noteq> \<langle>y,fy\<rangle> \<or> \<langle>v,t\<rangle> = \<langle>z,fy\<rangle>"
          then show "t \<epsilon> x \<and> t \<epsilon> u"
            by (metis \<open>\<langle>y,fy\<rangle> \<epsilon> f\<close> \<open>\<langle>z,y\<rangle> \<epsilon> f\<close> \<open>z \<noteq> y\<close> f(1,3) one_one_inj[of f z t]
                ordered_pair_unique[of _ t z fy] proper_subsetM_def[of u "x \<union>\<^sub>M {y}\<^sub>M"] rng_def'[of t f]
                setsuc_def'[of t x y] u)
        qed
        have "x = domM ?g'"
          using f(2) \<open>\<langle>y,fy\<rangle> \<epsilon> f\<close> one_oneD2[OF f(1)] \<open>\<not> y \<epsilon> x\<close> unfolding setext[of _ "domM _"] dom_def' g' setsuc_def'
            intersection_def'
          by (metis \<open>\<langle>z,y\<rangle> \<epsilon> f\<close> \<open>z \<noteq> y\<close> f(1) one_oneD3 ordered_pair_unique) 
        have "?u' \<approx>\<^sub>M x"
          unfolding set_equivalent_sym[of _ x] unfolding set_equivalent_def   
          by(rule exI[of _ ?g'], use \<open>one_oneM ?g'\<close> \<open>x = domM ?g'\<close> \<open>x \<inter>\<^sub>M u = rngM ?g'\<close> in blast)
        thus False
          using \<open>\<nexists>u. u \<subset>\<^sub>M x \<and> u \<approx>\<^sub>M x\<close> \<open>?u' \<subset>\<^sub>M x\<close> by blast 
      qed
    qed
  qed
  then show "\<forall>y. y \<subset>\<^sub>M x \<longrightarrow> \<not> x \<approx>\<^sub>M y"
    using set_equivalent_sym by blast
qed
    
text \<open>Corresponds to Corollary 4.3 in Kaye-Wong\<close>

lemma union_of_ords_mem:  assumes "\<forall> y. y \<epsilon> s \<longrightarrow> ordM y" "s \<noteq> \<emptyset>" 
  shows "\<Union>\<^sub>M s \<epsilon> s"
  unfolding setext[of s] union_def'
proof-
  obtain m where "m \<epsilon> s" and m_max: "\<forall> k. k \<epsilon> s \<longrightarrow> \<not> m \<subset>\<^sub>M k"
    using \<open>s \<noteq> \<emptyset>\<close> max_subset_ex by metis
  have aux: "z \<epsilon> m" if "v \<epsilon> s" "z \<epsilon> v" for v z
    using \<open>z \<epsilon> v\<close> assms(1)[rule_format, OF \<open>m \<epsilon> s\<close>] 
    assms(1)[rule_format, OF \<open>v \<epsilon> s\<close>]  m_max[rule_format, OF \<open>v \<epsilon> s\<close>]
    by (metis mem_nat_nat natM_def ordM_D1 ordM_total proper_subsetI subsetM_trans tarski) 
  have "m = \<Union>\<^sub>M s" 
    unfolding setext[of m] set_defs
    by (rule, rule, use \<open>m \<epsilon> s\<close> in blast, use aux in blast)
  thus "\<Union>\<^sub>M s \<epsilon> s"
    using \<open>m \<epsilon> s\<close> by blast
qed

lemma fun_images: assumes "SetFormulaPredicate P" and "\<forall> u. (\<exists>! v. P(\<Xi>(0:=u,1:=v)))"
  shows "\<exists> z. (\<forall> v. v \<epsilon> z \<longleftrightarrow> (\<exists> u. u \<epsilon> x \<and> P(\<Xi>(0:=u,1:=v))))" 
proof-
  from bounded_free[OF \<open>SetFormulaPredicate P\<close>]
  obtain m where "\<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> P \<Xi> = P \<Xi>'" 
    by blast
  hence m: "\<forall>\<Xi> \<Xi>'. (\<forall>i<m+2. \<Xi> i = \<Xi>' i) \<longrightarrow> P \<Xi> = P \<Xi>'" 
    by simp
  have small: "P (\<Xi>(Suc (Suc m) := x, 0 := u, Suc 0 := v)) = P (\<Xi>(0 := u, Suc 0 := v))" for u v x
    by (rule m[rule_format]) simp 
  let ?P = "\<lambda> X. \<exists>z. \<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> (X (m+2)) \<and> P (X(0 := u, 1 := v)))"
  have "SetFormulaPredicate ?P"
    using SFP_replace[OF \<open>SetFormulaPredicate P\<close> m].
  note aux_rule = setind_var[OF this, of "\<Xi>((m+2):= x)" "m+2", simplified, unfolded small, folded One_nat_def] 
  show "\<exists> z. (\<forall> v. v \<epsilon> z \<longleftrightarrow> (\<exists> u. u \<epsilon> x \<and> P(\<Xi>(0:=u,1:=v))))"
  proof (rule aux_rule[rule_format]) 
    show "\<exists>z. \<forall>v. \<not> v \<epsilon> z"
      using empty by blast
  next
    fix x y
    assume "\<exists>z. \<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> x \<and> P (\<Xi>(0 := u, 1 := v)))"
    then obtain z where z_def: "\<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> x \<and> P (\<Xi>(0 := u, 1 := v)))" 
      by blast
    obtain y' where "P (\<Xi>(0 := y, 1 := y'))"
      using assms(2) by blast
    have witness: "\<forall> v. v \<epsilon> z\<union>\<^sub>M{y'}\<^sub>M \<longleftrightarrow> (\<exists> u. u \<epsilon> x\<union>\<^sub>M{y}\<^sub>M \<and> P (\<Xi>(0 := u, 1 := v)))"
      unfolding setsuc_def' using  \<open>P (\<Xi>(0 := y, 1 := y'))\<close> assms(2) z_def by auto
    show "\<exists>z. \<forall>v. (v \<epsilon> z) = (\<exists>u. (u \<epsilon> x \<or> u = y) \<and> P (\<Xi>(0 := u, 1 := v)))"
      by (rule exI[of _ "z\<union>\<^sub>M{y'}\<^sub>M"]) (use witness in force) 
  qed
qed

sublocale L_fin
proof (unfold_locales, rule)
  assume "\<exists>x. \<emptyset> \<epsilon> x \<and> (\<forall>y. y \<epsilon> x \<longrightarrow> y \<union>\<^sub>M {y}\<^sub>M \<epsilon> x)"
  then obtain x where "\<emptyset> \<epsilon> x" and suc: "\<forall>y. y \<epsilon> x \<longrightarrow> y \<union>\<^sub>M {y}\<^sub>M \<epsilon> x" 
    by blast
  have SP: "SetProperty (\<lambda> x. regular x \<and> transM x)"
    unfolding SetProperty_def unfolding set_defs logsimps by rule+
  from sep_sp[OF this, rule_format, of x]
  obtain x' where x': "\<forall> u. u \<epsilon> x' \<longleftrightarrow> u \<epsilon> x \<and> regular u \<and> transM u"
    by blast
  have "x' \<noteq> \<emptyset>" "\<emptyset> \<epsilon> x'"
    using x' \<open>\<emptyset> \<epsilon> x\<close> by force+ 
  have suc': "y \<epsilon> x' \<longrightarrow> y \<union>\<^sub>M {y}\<^sub>M \<epsilon> x'" for y
    unfolding x'[rule_format] using suc by (simp add: regular_suc trans_suc) 
  from max_subset_ex[OF \<open>x' \<noteq> \<emptyset>\<close>]
  obtain xmax where "xmax \<epsilon> x'" "\<nexists> w. w \<epsilon> x' \<and> xmax \<subset>\<^sub>M w"
    by blast
  with suc'[rule_format, OF \<open>xmax \<epsilon> x'\<close>]
  have "\<not> xmax \<subset>\<^sub>M xmax \<union>\<^sub>M {xmax}\<^sub>M"
    by blast
  then have "xmax \<epsilon> xmax"
    unfolding set_defs setext[of xmax] by blast
  then show False
    using \<open>xmax \<epsilon> x'\<close> regular_not_self_mem x' by blast
qed    

end

sublocale L_setext_empty_power_union_repl_reg_fin \<subseteq> L_setext_empty_setsuc_setind
  by unfold_locales
  
text \<open>A metamathematical version of "A4 (induction and regularity)", Pudlák and Sochor 1984, p.572\<close>
locale L_setindregsch = set_signature +
  assumes setindregsch: "SetFormulaPredicate P \<Longrightarrow> 
    P(\<Xi>(0:= \<emptyset>)) \<longrightarrow> (\<forall> x y. P(\<Xi>(0:= x)) \<and> P(\<Xi>(0:= y)) \<longrightarrow> P(\<Xi>(0:= x\<union>\<^sub>M{y}\<^sub>M))) \<longrightarrow> (\<forall> x. P(\<Xi>(0:= x)))"

begin

lemma setindregsch_sp: assumes "SetProperty P" "P \<emptyset>" "\<forall> x y. P x \<and> P y \<longrightarrow> P (x\<union>\<^sub>M{y}\<^sub>M)"
  shows "\<forall> x. P x"
  using setindregsch[OF \<open>SetProperty P\<close>[unfolded SetProperty_def]] assms by force

lemma setindregsch_var: assumes "SetFormulaPredicate P" "P(\<Xi>(n:= \<emptyset>))" "\<forall> x y. P(\<Xi>(n:= x)) \<and> P(\<Xi>(n:= y)) 
  \<longrightarrow> P(\<Xi>(n:= x\<union>\<^sub>M{y}\<^sub>M))"
  shows "\<forall> x. P(\<Xi>(n:= x))"
proof
  fix x
  from bounded_free[OF \<open>SetFormulaPredicate P\<close>]
  obtain m where m: "P \<Xi> = P \<Xi>'" if "\<forall>i<m. \<Xi> i = \<Xi>' i" for \<Xi> \<Xi>'
    by blast
  let ?m = "Suc (n + m)"  
  let ?f = "id(0 := ?m, n:= 0)"
  let ?Q = "\<lambda> X. (P (\<lambda> b. X (?f  b)))"
  let ?X = "\<Xi>(?m:= \<Xi> 0)" 
  have sfpq:  "SetFormulaPredicate ?Q"
    using transform_variables[OF \<open>SetFormulaPredicate P\<close>] by simp
  have small: "\<forall> i < m. (\<Xi>(n := u)) i = (?X (0 := u)) (?f i)" for u
    by auto
  have equiv: "(P (\<Xi>(n := u))) \<longleftrightarrow> (?Q (?X (0 := u)))" for u
    by (rule m[of "\<Xi>(n := u)" "\<lambda> b. (?X (0 := u))(?f b)"]) fact
  show "P (\<Xi>(n := x))"
    unfolding equiv
    by (rule setindregsch[rule_format, OF sfpq, of "\<Xi>(Suc (n + m) := \<Xi> 0)"], unfold equiv[symmetric])
     (use assms in blast)+    
qed  

sublocale L_setind
  by unfold_locales (use setindregsch in blast)

end

locale L_setext_empty_setsuc_setindregsch = L_setext + L_empty + L_setsuc + L_setindregsch 

begin

sublocale L_setind
  using L_setind_def setindregsch by metis 
 
sublocale L_setext_empty_setsuc_setind
  by unfold_locales

lemma epsind_from_setindregsch_sp: assumes spp: "SetProperty P" and indp: "(\<forall> x. (\<forall>y. (y \<epsilon> x \<longrightarrow> P y))  \<longrightarrow>  P x)"
  shows "\<forall> x. P x"
proof-
  let ?Q = "\<lambda> x. \<forall> u. (u \<epsilon> x \<longrightarrow> P u)"
  have "SetFormulaPredicate (\<lambda>\<Xi>. P (\<Xi> m))" for m
     using spp[unfolded SetProperty_def] by (rule transform_variables) 
   have "SetProperty ?Q" 
     unfolding SetProperty_def set_defs logsimps by rule+ fact
   have "\<forall> v w. ?Q v \<and> ?Q w \<longrightarrow> ?Q  (v\<union>\<^sub>M{w}\<^sub>M)"  \<comment>\<open>use \<open>?Q\<close> w and \<open>indp\<close> to show P w\<close>
     using indp unfolding setsuc_def' by presburger
   from setindregsch_sp[OF \<open>SetProperty ?Q\<close> _ this]
   have " \<forall> x. ?Q x " 
     by force
   then show " \<forall> x. P x "
     using indp by blast 
 qed

lemma epsind_from_setindregsch: assumes sfp: "SetFormulaPredicate P" and indp: "(\<forall> x. (\<forall>y. (y \<epsilon> x \<longrightarrow> P(\<Xi>(0:=y))))  \<longrightarrow>  P(\<Xi>(0:=x)))"
  shows "\<forall> x. P(\<Xi>(0:=x))"
proof
  fix x
  from bounded_free[OF \<open>SetFormulaPredicate P\<close>]
  obtain m where "\<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> P \<Xi> = P \<Xi>'"
    by blast
  then have small: "P(\<Xi>(Suc m:=a, 0:= u)) = P(\<Xi>(0:= u))" for \<Xi> a u
    by simp
  let ?Q = "\<lambda> \<Xi>. \<forall> u. (u \<epsilon> (\<Xi> (Suc m)) \<longrightarrow> P(\<Xi>(0:=u)))"
  have sfpQ: "SetFormulaPredicate ?Q"
    by (rule SFP_all[of "\<lambda> \<Xi>. (\<Xi> 0) \<epsilon> (\<Xi> (m+1)) \<longrightarrow> P \<Xi>" 0, simplified])
    (unfold logsimps set_defs, (rule | fact)+)
  thm setindregsch_var[OF \<open>SetFormulaPredicate ?Q\<close>, of _ "Suc m", unfolded small, simplified]
  have "?Q (\<Xi> (0:=v))  \<and> ?Q (\<Xi> (0:=w)) \<longrightarrow> ?Q (\<Xi> (0:=(v\<union>\<^sub>M{w}\<^sub>M)))" for v w \<Xi> 
   \<comment>\<open>use ?Q w and indp to show P w\<close>
    unfolding setsuc_def' using indp[rule_format] by simp
  from setindregsch_var[OF \<open>SetFormulaPredicate ?Q\<close>, of _ "Suc m", unfolded small, simplified]
  have " ?Q (\<Xi>(Suc m:= x))"
    unfolding small fun_upd_same using indp by metis
  then show "P (\<Xi>(0 := x))"
     using indp unfolding small fun_upd_same by blast 
 qed

sublocale L_epsind
  by (unfold_locales) (use epsind_from_setindregsch in blast)

sublocale L_setext_empty_union_repl_pair_regsch
  by unfold_locales

sublocale L_regsch
  by unfold_locales

sublocale L_ts
  by unfold_locales  
    
end


subsection \<open>TarskiFin\<close>

locale L_setext_empty_power_sep_setsuc_tarski = L_setext + L_empty + L_power + L_sep + L_setsuc + L_tarski

begin

sublocale L_setext_empty_power
  by unfold_locales

sublocale L_setext_empty_setsuc 
  by unfold_locales

sublocale L_setind
proof (unfold_locales, rule, rule, rule)
  fix P \<Xi> x
  assume set_p: "SetFormulaPredicate P" and
    step: "(\<forall>x y. P (\<Xi>(0 := x)) \<longrightarrow> P (\<Xi>(0 := x \<union>\<^sub>M {y}\<^sub>M)))" and
    "P (\<Xi>(0 := \<emptyset>))"
  show "P (\<Xi>(0 := x))"
  proof (rule ccontr)
    assume "\<not> P (\<Xi>(0 := x))"
    obtain z where z_def: "\<And> u. (u \<epsilon> z) \<longleftrightarrow> (u \<epsilon> (\<PP> x) \<and> P (\<Xi>(0 := u)))" 
      using sep[OF set_p, rule_format, of "\<PP> x"] by blast   
    have "z \<noteq> \<emptyset>" 
      using z_def \<open>P (\<Xi>(0 := \<emptyset>))\<close> empty_is_empty empty_is_subset subsetM_def powerset_def' by blast
    have "z \<subseteq>\<^sub>M \<PP> x"
      by (simp add: subsetM_def z_def)
    have neg: "\<exists> v. v \<epsilon> z \<and> u \<subset>\<^sub>M v" if "u \<epsilon> z" for u
    proof-
      obtain y where "\<not> y \<epsilon> u" and "y \<epsilon> x"
        using  \<open>\<not> P (\<Xi>(0 := x))\<close> \<open>u \<epsilon> z\<close>[unfolded z_def] setext[of u x] unfolding subsetM_def powerset_def' by blast
      have "(u\<union>\<^sub>M{y}\<^sub>M) \<epsilon> z"
        using \<open>y \<epsilon> x\<close> step[rule_format,of u y] powerset_def' subsetM_def setsuc_def' that z_def by auto
      moreover have "u \<subset>\<^sub>M (u\<union>\<^sub>M{y}\<^sub>M)" 
        unfolding proper_subsetM_def setext[of u] setsuc_def' 
        using \<open>\<not> y \<epsilon> u\<close>  by blast
      ultimately show ?thesis
        by blast
    qed
    show False
      using tarski[rule_format, of x, unfolded tarski_fin_def, rule_format, of z] \<open>z \<subseteq>\<^sub>M \<PP> x\<close> neg \<open>z \<noteq> \<emptyset>\<close> 
      unfolding subsetM_def powerset_def' z_def
      using \<open>P (\<Xi>(0 := \<emptyset>))\<close> empty_is_empty by blast   
  qed   
qed

sublocale L_setext_empty_setsuc_setind
  by unfold_locales 

text \<open>Therefore also \<open>repl\<close>, see Běhounek 2.1.\<close>
sublocale L_repl
  by unfold_locales

text \<open>Corresponds to 4.3, in Běhounek\<close>
sublocale L_union
  by unfold_locales

end

locale L_setext_empty_power_repl_reg_tarski = L_setext + L_empty + L_power +  L_repl + L_reg + L_tarski

begin

sublocale L_setext_empty_power_repl
  by unfold_locales

sublocale L_setext_empty_power_sep_setsuc_tarski 
  by unfold_locales

sublocale L_setext_empty_power_union_repl_reg
  by unfold_locales

lemma max_mem: assumes "P n" "n \<epsilon> x" "SetProperty P"
  shows "\<exists> m. m \<epsilon> x \<and> P m \<and> (\<forall> k. k \<epsilon> x \<and> P k \<longrightarrow> \<not> m \<subset>\<^sub>M k)"
proof (rule ccontr)
  assume contr: "\<nexists>m. m \<epsilon> x \<and> P m \<and> (\<forall>k. k \<epsilon> x \<and> P k \<longrightarrow> \<not> m \<subset>\<^sub>M k)"
  hence chain: "\<exists> k. k \<epsilon> x \<and> P k \<and>  m \<subset>\<^sub>M k" if a: "P m" "m \<epsilon> x" for m
    using that by blast
  define y where "y = separationM x P"    
  from separ_def_sp[OF \<open>SetProperty P\<close>, of _ x, folded y_def]
  have y_def: "(u \<epsilon> y) \<longleftrightarrow> (u \<epsilon> x \<and> P u)" for u
    by simp
  have "y \<noteq> \<emptyset>"
    using assms y_def by force
  show False
    using max_subset_ex[OF \<open>y \<noteq> \<emptyset>\<close>] chain unfolding y_def by blast
qed

sublocale L_fin       
  by unfold_locales 

interpretation L_setext_empty_power_union_repl_reg_fin
  by unfold_locales

sublocale L_dedekind       
  by unfold_locales

end

subsection \<open>Summary of dependencies\<close>

theorem eps_ind_regsch_iff:
  "L_epsind mem \<longleftrightarrow> L_regsch mem"
proof
  assume "L_epsind mem"
  from L_epsind.epsind_regsch[OF this]
  show "L_regsch mem"
    by unfold_locales blast
next
  assume "L_regsch mem"
  from L_regsch.regsch_epsind[OF this]
  show "L_epsind mem"
    by unfold_locales
qed

text \<open>We give additional names to some important collections of axioms\<close>

locale ZFfin =  L_setext + L_empty + L_power + L_union +  L_repl + L_fin + L_epsind

begin
sublocale L_setext_empty_power_union_repl_reg_fin
  by unfold_locales
sublocale L_regsch
  by unfold_locales
sublocale L_reg
  by unfold_locales
sublocale L_setsuc
  by unfold_locales
sublocale L_sep
  by unfold_locales
sublocale L_setind
  by unfold_locales
sublocale L_dedekind
  by unfold_locales
sublocale L_tarski
  by unfold_locales
end

text \<open>This is the list of axioms for Vopěnka's "set universe", set part of AST.\<close>
locale ASTset = L_setext + L_empty +  L_setsuc + L_setind + L_regsch

begin

sublocale ZFfin
proof-
  interpret L_setext_empty_setsuc_setind
    by unfold_locales
  interpret L_epsind
    by (simp add: L_regsch_axioms eps_ind_regsch_iff) 
  show "ZFfin (\<epsilon>)"
    by unfold_locales
qed

sublocale L_setindregsch
proof (unfold_locales, rule, rule, rule)
  fix P :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool" and \<Xi> and x
  let ?P = "\<lambda> y. P (\<Xi>(0 := y))"
  assume sfp: "SetFormulaPredicate P"
  show "?P x" if "?P \<emptyset>" and  step: "(\<forall>x y. ?P x \<and> ?P y \<longrightarrow> ?P (x \<union>\<^sub>M {y}\<^sub>M))"
  proof-
    \<comment>\<open>In order to complete the proof by \<open>\<epsilon>\<close>-induction, it is enough to show that all sets inherit the property \<open>?P\<close>. 
       Call this inheritance property \<open>Q\<close>\<close>
    let ?Q = "\<lambda> w. (\<forall> u. u \<epsilon> w \<longrightarrow> ?P u) \<longrightarrow> ?P w"
      \<comment>\<open>We show that all sets satisfy \<open>Q\<close> by set-induction.\<close>

\<comment> \<open>But first some work has to be done. Note that \<open>?Q\<close> depends on free variables present in \<open>P\<close>.
  We therefore have to reformulate \<open>?Q\<close> to reflect this. 
  We formulate \<open>Q\<close> as a property of a fresh variable \<open>\<Xi> (m+1)\<close>\<close>
    from bounded_free[OF sfp]
    obtain m where m: "\<forall>\<Xi> \<Xi>'. (\<forall>i<m. \<Xi> i = \<Xi>' i) \<longrightarrow> P \<Xi> = P \<Xi>'" 
      by blast
    have fresh: " P (\<Xi>(m + k := a, 0 := b)) =  P (\<Xi>(0 := b))" for a b k \<Xi>
      \<comment> \<open>Indeed, \<open>P\<close> does not depend on any \<open>\<Xi> (m+k)\<close>\<close> 
      using m[rule_format, of "\<Xi>(m + k := a, 0 := b)" "\<Xi>(0 := b)"] by simp  

    let ?Q' = "\<lambda> \<Xi>. (\<forall> u. u \<epsilon> \<Xi> (m+1) \<longrightarrow> P (\<Xi>(0 := u))) \<longrightarrow> P (\<Xi>(0 := \<Xi> (m+1)))"
      \<comment> \<open>Q' \<Xi> now says: \<open>x\<^sub>m\<^sub>+\<^sub>1\<close> inherits \<open>P\<close> from its elements\<close>
    have "SetFormulaPredicate ?Q'"
      \<comment> \<open>The technical part: showing that \<open>?Q'\<close> is set formula predicate\<close>
    proof-
      have "SetFormulaPredicate (\<lambda>\<Xi>. \<forall>u. u \<epsilon> \<Xi> (Suc m) \<longrightarrow> P (\<Xi>(0 := u)))"
        by (rule SFP_all[of "\<lambda>\<Xi>. \<Xi> (m+2) \<epsilon> \<Xi> (Suc m) \<longrightarrow> P (\<Xi>(0 := \<Xi>(m+2)))" "m+2", 
              simplified fun_upd_same fun_upd_other, unfolded fresh])
          (unfold logsimps, rule+, fact) 
      show "SetFormulaPredicate ?Q'"
        unfolding logsimps by (rule | fact | simp)+ 
    qed
      \<comment>\<open>This yields the desired form of the induction in terms of \<open>?Q\<close>\<close>
    have Q_ind_rule: "?Q \<emptyset> \<Longrightarrow> (\<forall> x y. ?Q x \<longrightarrow> ?Q (x \<union>\<^sub>M {y}\<^sub>M)) \<Longrightarrow> \<forall> x. ?Q x"
      using setind_var[rule_format, OF \<open>SetFormulaPredicate ?Q'\<close>, of \<Xi> "m+1"] 
      unfolding fresh fun_upd_same by (rule, blast+) 

\<comment>\<open>Back to the main proof.\<close>
    have "\<forall> w. ?Q w"
    proof (rule Q_ind_rule)
      show "?Q \<emptyset>"
        using \<open>?P \<emptyset>\<close> by blast
          \<comment> \<open>the empty set inherits \<open>P\<close>, since it satisfies \<open>P\<close>\<close>
      show "\<forall> x y. ?Q x \<longrightarrow> ?Q (x \<union>\<^sub>M {y}\<^sub>M)"
      proof (rule, rule, rule, rule)
        fix x y
        assume \<open>?Q x\<close> and "\<forall>u. u \<epsilon> x \<union>\<^sub>M {y}\<^sub>M \<longrightarrow> ?P u" 
        hence "?P x" "?P y"
          using \<open>?Q x\<close> unfolding setsuc_def' by blast+
        thus "?P (x \<union>\<^sub>M {y}\<^sub>M)"
          using step by blast
      qed
    qed
    thus "?P x"
      using epsind[OF \<open>SetFormulaPredicate P\<close>] unfolding fun_upd_same fresh by metis
  qed
qed

end

lemma (in ZFfin) zffin_ast: "ASTset (\<epsilon>)"
  by unfold_locales

theorem repl_implies_sep:
  shows "L_setext_empty_repl (\<epsilon>) \<Longrightarrow> L_sep (\<epsilon>)"
proof-
  assume "L_setext_empty_repl (\<epsilon>)"
  then interpret L_setext_empty_repl "(\<epsilon>)".
  show "L_sep (\<epsilon>)"
    by unfold_locales
qed

theorem sep_implies_repl:
  shows "L_setext_empty_power_sep_setsuc_tarski (\<epsilon>) \<Longrightarrow> L_repl (\<epsilon>)"
proof-
  assume "L_setext_empty_power_sep_setsuc_tarski (\<epsilon>)"
  then interpret L_setext_empty_power_sep_setsuc_tarski "(\<epsilon>)".
  show "L_repl (\<epsilon>)"
    by unfold_locales
qed

theorem (in L_setext_empty_setsuc) 
  shows setind_implies_tarski: "L_setind (\<epsilon>) \<Longrightarrow> L_tarski (\<epsilon>)" and
        setind_implies_fin_by_setsuc: "L_setind (\<epsilon>) \<Longrightarrow> L_fin (\<epsilon>)"  
proof-
  assume "L_setind (\<epsilon>)"
  then interpret L_setind
    by blast
  interpret L_setext_empty_setsuc_setind
    by unfold_locales 
  interpret L_tarski
    by unfold_locales 
  interpret L_tarski
    by unfold_locales 
  show "L_tarski (\<epsilon>)" "L_fin (\<epsilon>)"
    by unfold_locales
qed    

theorem (in L_setext_empty_power_union_repl)
   dedekind_implies_fin: "L_dedekind (\<epsilon>) \<Longrightarrow> L_fin (\<epsilon>)"
proof-
  assume "L_dedekind (\<epsilon>)"
  then interpret L_dedekind.
  interpret L_setext_empty_power_union_repl_dedekind
    by unfold_locales
  show "L_fin (\<epsilon>)"
    by (simp add: L_fin_axioms)
qed

theorem (in L_setext_empty_power_union_repl_reg)
        fin_implies_tarski: "L_fin (\<epsilon>) \<Longrightarrow> L_tarski (\<epsilon>)" and
        tarski_implies_fin: "L_tarski (\<epsilon>) \<Longrightarrow> L_fin (\<epsilon>)" and
        fin_implies_setind: "L_fin (\<epsilon>) \<Longrightarrow> L_setind (\<epsilon>)" and
        setind_implies_fin: "L_setind (\<epsilon>) \<Longrightarrow> L_fin (\<epsilon>)" and
        fin_implies_dedekind: "L_fin (\<epsilon>) \<Longrightarrow> L_dedekind (\<epsilon>)"
proof-
  assume "L_fin (\<epsilon>)"
  then interpret L_fin "(\<epsilon>)". 
  interpret L_setext_empty_power_union_repl_reg_fin "(\<epsilon>)"
     by unfold_locales 
  show "L_tarski (\<epsilon>)" 
    by unfold_locales 
  show "L_dedekind (\<epsilon>)" 
    by unfold_locales 
  show "L_setind (\<epsilon>)" 
    by unfold_locales 
next
  assume "L_tarski (\<epsilon>)"
  then interpret L_tarski "(\<epsilon>)". 
  interpret L_setext_empty_power_repl_reg_tarski "(\<epsilon>)"
     by unfold_locales 
  show "L_fin (\<epsilon>)" 
    by unfold_locales 
next
  assume "L_setind (\<epsilon>)" 
  then interpret L_setind "(\<epsilon>)"
    by blast
  interpret L_setsuc "(\<epsilon>)"
    by unfold_locales (simp add: set_suc)
  interpret L_setext_empty_setsuc "(\<epsilon>)"
    by unfold_locales
  from setind_implies_tarski[OF \<open>L_setind (\<epsilon>)\<close>]  
  interpret L_tarski "(\<epsilon>)".
  interpret L_setext_empty_power_repl_reg_tarski "(\<epsilon>)"
     by unfold_locales 
  show "L_fin (\<epsilon>)"
    by unfold_locales 
qed

theorem  (in L_setext_sep_reg) Kaye_Wong_5_4A: 
  "L_ts (\<epsilon>) \<Longrightarrow> L_epsind (\<epsilon>)"
proof-
  assume "L_ts (\<epsilon>)"
  then interpret L_ts "(\<epsilon>)".
  interpret L_setext_sep_reg_ts
    by unfold_locales
  interpret L_regsch
    by unfold_locales
  show "L_epsind (\<epsilon>)"
    using L_epsind_def regsch_epsind by blast
qed

theorem  (in L_setext_empty_union_repl_pair) Kaye_Wong_5_4B: 
  "L_epsind (\<epsilon>) \<Longrightarrow> L_ts (\<epsilon>)"
proof-
  assume "L_epsind (\<epsilon>)"
  then interpret L_epsind "(\<epsilon>)".
  interpret L_setext_empty_union_repl_pair_regsch
    by unfold_locales  
  show "L_ts (\<epsilon>)"
    using L_ts_axioms.   
qed

text \<open>A81 + A82 |- A8, in Sochor\<close>
theorem (in L_setext_sep_reg_ts) SochorA:
  "L_regsch (\<epsilon>)"
  by unfold_locales 

theorem (in L_setext_empty_union_repl_pair_regsch) SochorB:
 "L_ts (\<epsilon>)"
  by unfold_locales

theorem (in L_setext_empty_setsuc_setind) AST_dedekind:
  "L_dedekind (\<epsilon>)"
  by unfold_locales 

end