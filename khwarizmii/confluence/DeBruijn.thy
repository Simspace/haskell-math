(*  Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen
*)

(*:maxLineLen=80:*)

theory DeBruijn
  imports Main
          "~~/src/HOL/Library/Lattice_Syntax"
begin

sledgehammer_params [smt_proofs = false]

declare [[syntax_ambiguity_warning = false]]

section \<open>Lambda Calculus Using de Bruijn Notation\<close>

subsection \<open>Grammar\<close>

datatype dB =
    Variable nat ("\<langle>_\<rangle>" [100] 100)
  | Application dB dB (infixl "\<cdot>" 200)
  | Abstraction dB ("\<^bold>\<lambda>")

subsection \<open>Substitution\<close>

primrec
  lift :: "dB \<Rightarrow> nat \<Rightarrow> dB"
where
    "lift (\<langle>i\<rangle>) k = (if i < k then \<langle>i\<rangle> else \<langle>(i + 1)\<rangle>)"
  | "lift (s \<cdot> t) k = lift s k \<cdot> lift t k"
  | "lift (\<^bold>\<lambda> s) k = \<^bold>\<lambda> (lift s (k + 1))"

primrec
  subst :: "dB \<Rightarrow> nat \<Rightarrow> dB \<Rightarrow> dB"  ("_[_ '\<^bold>\<mapsto> _]" [300, 0, 0] 300)
  where
    subst_Var: "(\<langle>i\<rangle>)[k \<^bold>\<mapsto> s] =
      (if k < i then \<langle>(i - 1)\<rangle> else if i = k then s else \<langle>i\<rangle>)"
  | subst_App: "(t \<cdot> u)[k \<^bold>\<mapsto> s] = t[k \<^bold>\<mapsto> s] \<cdot> u[k \<^bold>\<mapsto> s]"
  | subst_Abs: "(\<^bold>\<lambda> t)[k \<^bold>\<mapsto> s] = \<^bold>\<lambda> (t [k + 1 \<^bold>\<mapsto> lift s 0])"

declare subst_Var [simp del]
declare if_not_P [simp] not_less_eq [simp]

subsection \<open>Derived Substitution Rules\<close>

lemma subst_eq [simp]: "(\<langle>k\<rangle>)[k \<^bold>\<mapsto> u] = u"
  by (simp add: subst_Var)

lemma subst_gt [simp]: "i < j \<Longrightarrow> (\<langle>j\<rangle>)[i \<^bold>\<mapsto> u] = \<langle>(j - 1)\<rangle>"
  by (simp add: subst_Var)

lemma subst_lt [simp]: "j < i \<Longrightarrow> (\<langle>j\<rangle>)[i \<^bold>\<mapsto> u] = \<langle>j\<rangle>"
  by (simp add: subst_Var)

lemma lift_lift:
    "i < k + 1 \<Longrightarrow> lift (lift t i) (Suc k) = lift (lift t k) i"
  by (induct t arbitrary: i k) auto

lemma lift_subst [simp]:
    "j < i + 1 \<Longrightarrow> lift (t[j \<^bold>\<mapsto> s]) i = (lift t (i + 1))[j \<^bold>\<mapsto> lift s i]"
  by (induct t arbitrary: i j s)
    (simp_all add: diff_Suc subst_Var lift_lift split: nat.split)

lemma lift_subst_lt:
    "i < j + 1 \<Longrightarrow> lift (t[j \<^bold>\<mapsto> s]) i = (lift t i)[j+1 \<^bold>\<mapsto> lift s i]"
  by (induct t arbitrary: i j s) (simp_all add: subst_Var lift_lift)

lemma subst_lift [simp]:
    "(lift t k)[k \<^bold>\<mapsto> s] = t"
  by (induct t arbitrary: k s) simp_all

lemma subst_subst:
    "i < j + 1 \<Longrightarrow> t[j+1 \<^bold>\<mapsto> lift v i][i \<^bold>\<mapsto> u[j \<^bold>\<mapsto> v]] = t[i \<^bold>\<mapsto> u][j \<^bold>\<mapsto> v]"
  by (induct t arbitrary: i j u v)
    (simp_all 
      add: diff_Suc subst_Var lift_lift [symmetric] lift_subst_lt
      split: nat.split)

subsection \<open>Small-Step Beta Reduction\<close>

inductive beta :: "dB \<Rightarrow> dB \<Rightarrow> bool"  (infixl "\<rightarrow>\<^sub>\<beta>" 50)
  where
    beta [simp, intro!]: "\<^bold>\<lambda> s \<cdot> t \<rightarrow>\<^sub>\<beta> s[0 \<^bold>\<mapsto> t]"
  | appL [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> s \<cdot> u \<rightarrow>\<^sub>\<beta> t \<cdot> u"
  | appR [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> u \<cdot> s \<rightarrow>\<^sub>\<beta> u \<cdot> t"
  | abs [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> \<^bold>\<lambda> s \<rightarrow>\<^sub>\<beta> \<^bold>\<lambda> t"

inductive_cases beta_cases [elim!]:
  "Var i \<rightarrow>\<^sub>\<beta> t"
  "\<^bold>\<lambda> r \<rightarrow>\<^sub>\<beta> s"
  "s \<cdot> t \<rightarrow>\<^sub>\<beta> u"

subsection \<open>Derived Small-Step Beta Reduction Rules\<close>

theorem lift_preserves_beta [simp]:
    "r \<rightarrow>\<^sub>\<beta> s \<Longrightarrow> lift r i \<rightarrow>\<^sub>\<beta> lift s i"
  by (induct arbitrary: i set: beta) auto

theorem subst_preserves_beta [simp, intro!]:
    "r \<rightarrow>\<^sub>\<beta> s \<Longrightarrow> r[i \<^bold>\<mapsto> t] \<rightarrow>\<^sub>\<beta> s[i \<^bold>\<mapsto> t]"
  by (induct arbitrary: t i set: beta)
     (simp_all add: subst_subst [symmetric])

subsection \<open>Transitive Beta Reduction\<close>

abbreviation
  beta_reds :: "dB \<Rightarrow> dB \<Rightarrow> bool"  (infixl "\<rightarrow>\<^sub>\<beta>\<^sup>*" 50) where
  "s \<rightarrow>\<^sub>\<beta>\<^sup>* t == beta\<^sup>*\<^sup>* s t"

subsection \<open>Transitive Beta Reduction Rules\<close>

lemma rtrancl_beta_Abs [intro!]:
    "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<Longrightarrow> \<^bold>\<lambda> s \<rightarrow>\<^sub>\<beta>\<^sup>* \<^bold>\<lambda> s'"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_AppL:
    "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<Longrightarrow> s \<cdot> t \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<cdot> t"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_AppR:
    "t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> s \<cdot> t \<rightarrow>\<^sub>\<beta>\<^sup>* s \<cdot> t'"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_App [intro]:
    "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<Longrightarrow> t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> s \<cdot> t \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<cdot> t'"
  by (blast intro!: rtrancl_beta_AppL rtrancl_beta_AppR intro: rtranclp_trans)

theorem rtancl_lift_preserves_beta: 
    "r \<rightarrow>\<^sub>\<beta>\<^sup>* s \<Longrightarrow> lift r i \<rightarrow>\<^sub>\<beta>\<^sup>* lift s i"
  by (induct rule: rtranclp.induct,
      blast, 
      simp add: rtranclp.rtrancl_into_rtrancl)

theorem rtrancl_subst_preserves_beta: 
    "r \<rightarrow>\<^sub>\<beta>\<^sup>* s \<Longrightarrow> r[i \<^bold>\<mapsto> t] \<rightarrow>\<^sub>\<beta>\<^sup>* s[i \<^bold>\<mapsto> t]"
  by (induct rule: rtranclp.induct, 
      blast, 
      meson rtranclp.simps subst_preserves_beta)

theorem rtancl_subst_preserves_beta_inner: 
    "r \<rightarrow>\<^sub>\<beta>\<^sup>* s \<Longrightarrow> t[i \<^bold>\<mapsto> r] \<rightarrow>\<^sub>\<beta>\<^sup>* t[i \<^bold>\<mapsto> s]"
proof -
  {
    fix r s t
    have "r \<rightarrow>\<^sub>\<beta> s \<Longrightarrow> t[i \<^bold>\<mapsto> r] \<rightarrow>\<^sub>\<beta>\<^sup>* t[i \<^bold>\<mapsto> s]"
      by (induct t arbitrary: r s i,
          simp add: subst_Var r_into_rtranclp,
          simp add: rtrancl_beta_App, 
          simp add: rtrancl_beta_Abs)
  } note \<dagger> = this
  show "r \<rightarrow>\<^sub>\<beta>\<^sup>* s \<Longrightarrow> t[i \<^bold>\<mapsto> r] \<rightarrow>\<^sub>\<beta>\<^sup>* t[i \<^bold>\<mapsto> s]"
    by (induct rule: rtranclp.induct, 
        blast,
        metis \<dagger> rtranclp.rtrancl_into_rtrancl rtranclp_idemp)
qed

subsection \<open>Confluence Principles\<close>

subsubsection \<open>Definitions\<close>

definition square where
  "square R S T U = (\<forall>x y. R x y \<longrightarrow> (\<forall>z. S x z \<longrightarrow> (\<exists>u. T y u \<and> U z u)))"

definition commute where
  "commute R S = square R S S R"

definition diamond where
  "diamond R = commute R R"

abbreviation confluent where
  "confluent R \<equiv> diamond (R\<^sup>*\<^sup>*)"

abbreviation weakly_confluent where
  "weakly_confluent R \<equiv> square R R (R\<^sup>*\<^sup>*) (R\<^sup>*\<^sup>*)"

no_notation converse ("(_\<inverse>)" [1000] 999)
notation conversep  ("(_\<inverse>)" [1000] 1000)

no_notation rtrancl ("(_\<^sup>*)" [1000] 1000)
notation rtranclp  ("(_\<^sup>*)" [1000] 1000)

definition
  Church_Rosser :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "Church_Rosser R =
    (\<forall>p q. (R \<squnion> R\<inverse>)\<^sup>*\<^sup>* p q \<longleftrightarrow> (\<exists>x. R\<^sup>*\<^sup>* p x \<and> R\<^sup>*\<^sup>* q x))"

subsubsection \<open>Church-Rosser Properties\<close>

lemma common_reduction_to_equiv:
  assumes 
    "R\<^sup>* x z"
    "R\<^sup>* y z"
  shows "(R \<squnion> R\<inverse>)\<^sup>* x y"
proof -
  have "(R \<squnion> R\<inverse>)\<^sup>* x z"
    by (metis \<open>R\<^sup>* x z\<close> mono_rtranclp sup2I1)
  moreover have "(R \<squnion> R\<inverse>)\<^sup>*\<^sup>* z y"
    by (metis (no_types, lifting) 
          \<open>R\<^sup>*\<^sup>* y z\<close> 
          conversep_conversep 
          mono_rtranclp 
          rtranclp_converseD 
          sup2CI)
  ultimately show ?thesis
    by auto
qed

lemma Church_Rosser_alt_def: 
  "Church_Rosser R =
    (\<forall>x y. (R \<squnion> R\<inverse>)\<^sup>*\<^sup>* x y \<longrightarrow> (\<exists>z. R\<^sup>*\<^sup>* x z \<and> R\<^sup>*\<^sup>* y z))"
  unfolding Church_Rosser_def
  by (rule iffI, blast, meson common_reduction_to_equiv)

lemma common_ancestor_to_equiv:
  assumes
    "R\<^sup>*\<^sup>* x y"
    "R\<^sup>*\<^sup>* x z"
  shows "(R \<squnion> R\<inverse>)\<^sup>*\<^sup>* y z"
proof -
  have "(R \<squnion> R\<inverse>)\<^sup>*\<^sup>* y x"
    by (meson 
          \<open>R\<^sup>*\<^sup>* x y\<close>
          common_reduction_to_equiv 
          rtranclp.rtrancl_refl)
  moreover have "(R \<squnion> R\<inverse>)\<^sup>*\<^sup>* x z"
    by (metis \<open>R\<^sup>*\<^sup>* x z\<close> mono_rtranclp sup2I1)
  ultimately show ?thesis by auto
qed

lemma Church_Rosser_confluent: "confluent R \<longleftrightarrow> Church_Rosser R"
unfolding square_def commute_def diamond_def Church_Rosser_alt_def
proof (rule iffI; (rule allI | rule impI)+ )
  fix x y z
  assume 
    "\<forall>x y. (R \<squnion> R\<inverse>)\<^sup>*\<^sup>* x y \<longrightarrow> (\<exists>z. R\<^sup>*\<^sup>* x z \<and> R\<^sup>*\<^sup>* y z)"
    "R\<^sup>*\<^sup>* x y"
    "R\<^sup>*\<^sup>* x z"
  thus "\<exists>u. R\<^sup>*\<^sup>* y u \<and> R\<^sup>*\<^sup>* z u"
    by (meson common_ancestor_to_equiv)
next
  fix x y
  assume "(R \<squnion> R\<inverse>)\<^sup>*\<^sup>* x y" 
         "\<forall>x y. R\<^sup>*\<^sup>* x y \<longrightarrow> (\<forall>z. R\<^sup>*\<^sup>* x z \<longrightarrow> (\<exists>u. R\<^sup>*\<^sup>* y u \<and> R\<^sup>*\<^sup>* z u))"
  thus "\<exists>z. R\<^sup>*\<^sup>* x z \<and> R\<^sup>*\<^sup>* y z" 
    by (induct rule: rtranclp.induct) 
       (auto, meson r_into_rtranclp rtranclp_trans)
qed

subsubsection \<open>Primitive Properties\<close>

lemma square_sym: "square R S T U \<Longrightarrow> square S R U T"
  by (metis (mono_tags, hide_lams) square_def)

lemma square_subset: 
  assumes "square R S T U"
  and "T \<le> T'"
  shows "square R S T' U"
    using assms
    unfolding square_def
    by (meson predicate2D_conj)

lemma square_reflcl:
  assumes "square R S T (R\<^sup>=\<^sup>=)"
  and "S \<le> T"
  shows "square (R\<^sup>=\<^sup>=) S T (R\<^sup>=\<^sup>=)"
    using assms
    unfolding square_def
    by blast

lemma square_rtrancl:
  assumes "square R S S T"
  shows "square (R\<^sup>*\<^sup>*) S S (T\<^sup>*\<^sup>*)"
  unfolding square_def
proof (intro strip, erule rtranclp_induct)
  fix x y z
  assume "S x z"
  thus "\<exists>u. S x u \<and> T\<^sup>*\<^sup>* z u"
    by blast
next
  fix x y z y' z'
  assume "S x z"
         "R\<^sup>*\<^sup>* x y'" 
         "R y' z'" 
         "\<exists>u. S y' u \<and> T\<^sup>*\<^sup>* z u"
  thus "\<exists>u'. S z' u' \<and> T\<^sup>*\<^sup>* z u'"
    using \<open>square R S S T\<close>
    unfolding square_def
    by (meson rtranclp.rtrancl_into_rtrancl)
qed

lemma square_rtrancl_reflcl_commute:
  "square R S (S\<^sup>*\<^sup>*) (R\<^sup>=\<^sup>=) \<Longrightarrow> commute (R\<^sup>*\<^sup>*) (S\<^sup>*\<^sup>*)"
  unfolding commute_def
  by (metis 
       predicate2I 
       r_into_rtranclp 
       rtranclp_idemp 
       rtranclp_reflclp 
       square_reflcl 
       square_rtrancl 
       square_sym)

lemma commute_sym: "commute R S \<Longrightarrow> commute S R"
  unfolding commute_def square_def
  by blast

lemma commute_rtrancl: "commute R S \<Longrightarrow> commute (R\<^sup>*\<^sup>*) (S\<^sup>*\<^sup>*)"
  unfolding commute_def
  by (blast intro: square_rtrancl square_sym)

lemma commute_Un:
  "commute R T \<Longrightarrow> commute S T \<Longrightarrow> commute (R \<squnion> S) T"
  unfolding commute_def square_def
  by (metis sup2CI sup2E)

lemma diamond_Un:
  assumes "diamond R"
  and "diamond S" 
  and "commute R S" 
  shows "diamond (sup R S)"
    using assms
    unfolding diamond_def
    by (blast intro: commute_Un commute_sym)

lemma diamond_confluent: "diamond R \<Longrightarrow> confluent R"
  unfolding diamond_def
  by (simp add: commute_rtrancl)
  
lemma square_reflcl_confluent:
    "square R R (R\<^sup>=\<^sup>=) (R\<^sup>=\<^sup>=) \<Longrightarrow> confluent R"
  unfolding diamond_def commute_def
  by (metis 
       inf_sup_ord(3) 
       rtranclp_reflclp 
       square_reflcl 
       square_rtrancl 
       square_sym)
  
lemma confluent_Un:
  assumes "confluent R"
  and "confluent S"
  and "commute (R\<^sup>*\<^sup>*) (S\<^sup>*\<^sup>*)"
  shows "confluent (R \<squnion> S)"
    using assms
    by (metis diamond_Un diamond_confluent rtranclp_sup_rtranclp)

lemma diamond_to_confluence:
  assumes "diamond R"
  and "T \<le> R"
  and "R \<le> T\<^sup>*\<^sup>*"
  shows "confluent T"
    using assms diamond_confluent rtranclp_subset 
    by fastforce

lemma basic_diamond_to_confluence:
  assumes "diamond R"
  and "T \<le> R"
  and "R \<le> T\<^sup>*\<^sup>*"
  shows "confluent R"
    using assms diamond_confluent rtranclp_subset 
    by fastforce

theorem newman:
  assumes "wfP R\<inverse>"
  and "weakly_confluent R"
  shows "confluent R"
proof -
  {
    fix a b c
    have "R\<^sup>*\<^sup>* a b \<Longrightarrow> R\<^sup>*\<^sup>* a c \<Longrightarrow> \<exists>d. R\<^sup>*\<^sup>* b d \<and> R\<^sup>*\<^sup>* c d"
      using \<open>wfP R\<inverse>\<close>
    proof (induct arbitrary: b c)
      case (less x b c)
      have "R\<^sup>*\<^sup>* x c" by fact
      have "R\<^sup>*\<^sup>* x b" by fact 
      thus ?case
      proof (rule converse_rtranclpE)
        assume "x = b"
        thus ?thesis
          using \<open>R\<^sup>*\<^sup>* x c\<close> by blast
      next
        fix y
        assume "R x y"
        and "R\<^sup>*\<^sup>* y b"
        from \<open>R\<^sup>*\<^sup>* x c\<close> show "\<exists>d. R\<^sup>*\<^sup>* b d \<and> R\<^sup>*\<^sup>* c d"
        proof (rule converse_rtranclpE)
          assume "x = c"
          thus ?thesis
            using \<open>R\<^sup>*\<^sup>* x b\<close> by blast 
        next
          fix z
          assume "R\<^sup>*\<^sup>* z c" and "R x z"
          from this obtain u where "R\<^sup>*\<^sup>* y u" and "R\<^sup>*\<^sup>* z u"
            using \<open>weakly_confluent R\<close>
            unfolding square_def
            using \<open>R x y\<close> by blast
          from this  obtain v where "R\<^sup>*\<^sup>* b v" and "R\<^sup>*\<^sup>* u v"
            by (meson conversep.intros less.hyps \<open>R x y\<close> \<open>R\<^sup>*\<^sup>* y b\<close>)
          from this obtain w where "R\<^sup>*\<^sup>* v w" and "R\<^sup>*\<^sup>* c w"
            by (meson 
                  \<open>R x z\<close> 
                  \<open>R\<^sup>*\<^sup>* z c\<close> 
                  \<open>R\<^sup>*\<^sup>* z u\<close> 
                  conversep.intros 
                  less.hyps 
                  rtranclp_trans)
          thus ?thesis
            by (meson \<open>R\<^sup>*\<^sup>* b v\<close> rtranclp_trans) 
        qed
      qed
    qed
  }
  thus ?thesis
    unfolding diamond_def commute_def square_def
    by auto
qed

section \<open>Confluence Of Beta Reduction\<close>

text \<open>Here we present a proof of the confluence confluence of \<open>\<rightarrow>\<^sub>\<beta>\<close>.  
      This proof is attributed to William Tait and Per Martin-Löf. 
      The technique has been described in
      @{cite takahashiParallelReductionsLCalculus1995}\<close>

subsection \<open>Parallel Reduction\<close>

inductive par_beta :: "dB \<Rightarrow> dB \<Rightarrow> bool"  (infixl "\<Rrightarrow>\<^sub>\<beta>" 50)                                                                                         
  where                                                                                                                                            
    var [simp, intro!]: "(\<langle>i\<rangle>) \<Rrightarrow>\<^sub>\<beta> (\<langle>i\<rangle>)"                                                                                                           
  | abs [simp, intro!]: "s \<Rrightarrow>\<^sub>\<beta> t \<Longrightarrow> \<^bold>\<lambda> s \<Rrightarrow>\<^sub>\<beta> \<^bold>\<lambda> t"                                                                                                
  | app [simp, intro!]: "\<lbrakk> s \<Rrightarrow>\<^sub>\<beta> s'; t \<Rrightarrow>\<^sub>\<beta> t' \<rbrakk> \<Longrightarrow> s \<cdot> t \<Rrightarrow>\<^sub>\<beta> s' \<cdot> t'"                                                              
  | beta [simp, intro!]: "\<lbrakk> s \<Rrightarrow>\<^sub>\<beta> s'; t \<Rrightarrow>\<^sub>\<beta> t' \<rbrakk> \<Longrightarrow> (\<^bold>\<lambda> s) \<cdot> t \<Rrightarrow>\<^sub>\<beta> s'[0 \<^bold>\<mapsto> t']"                                                              
                                                                                                                                                   
inductive_cases par_beta_cases [elim!]:                                                                                                            
  "(\<langle>i\<rangle>) \<Rrightarrow>\<^sub>\<beta> t"                                                                                                                                     
  "\<^bold>\<lambda> s \<Rrightarrow>\<^sub>\<beta> \<^bold>\<lambda> t"                                                                                                                                 
  "(\<^bold>\<lambda> s) \<cdot> t \<Rrightarrow>\<^sub>\<beta> u"                                                                                                                       
  "s \<cdot> t \<Rrightarrow>\<^sub>\<beta> u"                                                                                                                             
  "\<^bold>\<lambda> s \<Rrightarrow>\<^sub>\<beta> t"

subsection \<open>Properties of Parallel Reduction\<close>

lemma par_beta_varL [simp]:                                                                                                                        
    "((\<langle>i\<rangle>) \<Rrightarrow>\<^sub>\<beta> t) = (t = (\<langle>i\<rangle>))"                                                                                                                   
  by blast

lemma par_beta_refl [simp]: "t \<Rrightarrow>\<^sub>\<beta> t"
  by (induct t) simp_all                                                                                                                           

lemma par_beta_lift [simp]:                                                                                                                        
    "t \<Rrightarrow>\<^sub>\<beta> t' \<Longrightarrow> lift t n \<Rrightarrow>\<^sub>\<beta> lift t' n"                                                                                              
  by (induct t arbitrary: t' n) fastforce+

lemma par_beta_subst:
    "s \<Rrightarrow>\<^sub>\<beta> s' \<Longrightarrow> t \<Rrightarrow>\<^sub>\<beta> t' \<Longrightarrow> t[n \<^bold>\<mapsto> s] \<Rrightarrow>\<^sub>\<beta> t'[n \<^bold>\<mapsto> s']"
  apply (induct t arbitrary: s s' t' n)
    apply (simp add: subst_Var)
   apply (erule par_beta_cases)
    apply (simp add: subst_subst [symmetric] 
            | fastforce intro!: par_beta_lift)+
  done

subsection \<open>Parallel Reduction is Intermediate To 
            Small-Step and Transitive Beta Reduction\<close>
                                                                                                                                                   
lemma beta_subset_par_beta: "(\<rightarrow>\<^sub>\<beta>) \<le> (\<Rrightarrow>\<^sub>\<beta>)"
  by (rule predicate2I, erule beta.induct) simp_all
                                                                                                                                                   
lemma beta_implies_par_beta: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> s \<Rrightarrow>\<^sub>\<beta> t"
  using beta_subset_par_beta by blast

lemma par_beta_subset_beta: "(\<Rrightarrow>\<^sub>\<beta>) \<le> (\<rightarrow>\<^sub>\<beta>\<^sup>*)"
  by (rule predicate2I, erule par_beta.induct)                                                                                                                    
     (blast, blast, blast, 
        blast del: rtranclp.rtrancl_refl intro: rtranclp.rtrancl_into_rtrancl) 

lemma par_beta_implies_transitive_beta: "s \<Rrightarrow>\<^sub>\<beta> t \<Longrightarrow> s \<rightarrow>\<^sub>\<beta>\<^sup>* t"
  using par_beta_subset_beta by blast
  
subsection \<open>Confluence Theorems Parallel Reduction And Beta Reduction\<close>

lemma diamond_par_beta: "diamond (\<Rrightarrow>\<^sub>\<beta>)"
  apply (unfold diamond_def commute_def square_def)
  apply (rule impI [THEN allI [THEN allI]])
  apply (erule par_beta.induct)
     apply (blast intro!: par_beta_subst)+
  done

lemma par_beta_confluent: "confluent (\<Rrightarrow>\<^sub>\<beta>)"
  by (simp add: diamond_confluent diamond_par_beta)

lemma beta_confluent: "confluent (\<rightarrow>\<^sub>\<beta>)"
  using 
    beta_subset_par_beta 
    diamond_par_beta 
    diamond_to_confluence 
    par_beta_subset_beta 
  by blast

section \<open>Equational Theory\<close>

inductive beta_equiv :: "dB \<Rightarrow> dB \<Rightarrow> bool"  (infixl "\<approx>\<^sub>\<beta>" 40) where
    refl [simp]: "t \<approx>\<^sub>\<beta> t"
  | subst [simp]: "(\<^bold>\<lambda> s) \<cdot> t \<approx>\<^sub>\<beta> s [ 0 \<^bold>\<mapsto> t]"
  | abs [simp]: "s \<approx>\<^sub>\<beta> t \<Longrightarrow> \<^bold>\<lambda> s \<approx>\<^sub>\<beta> \<^bold>\<lambda> t"
  | symm: "s \<approx>\<^sub>\<beta> t \<Longrightarrow> t \<approx>\<^sub>\<beta> s"
  | app [simp]: "s \<approx>\<^sub>\<beta> t \<Longrightarrow> p \<approx>\<^sub>\<beta> q \<Longrightarrow> s \<cdot> p \<approx>\<^sub>\<beta> t \<cdot> q" 
  | trans [simp]: "s \<approx>\<^sub>\<beta> t \<Longrightarrow> t \<approx>\<^sub>\<beta> u \<Longrightarrow> s \<approx>\<^sub>\<beta> u"

lemma beta_equiv_alt_def:
  "(p \<approx>\<^sub>\<beta> q) = ((\<rightarrow>\<^sub>\<beta>) \<squnion> (\<rightarrow>\<^sub>\<beta>)\<inverse>)\<^sup>*\<^sup>* p q"
proof (rule iffI)
  {
    fix s t
    have "((\<rightarrow>\<^sub>\<beta>) \<squnion> (\<rightarrow>\<^sub>\<beta>)\<inverse>)\<^sup>*\<^sup>* s t \<Longrightarrow> ((\<rightarrow>\<^sub>\<beta>) \<squnion> (\<rightarrow>\<^sub>\<beta>)\<inverse>)\<^sup>*\<^sup>* (\<^bold>\<lambda> s) (\<^bold>\<lambda> t)"
      by (induct set: rtranclp,
            blast, 
            metis 
              beta.abs 
              conversep_iff
              rtranclp.rtrancl_into_rtrancl
              sup2CI
              sup2E)
  } note \<dagger> = this
  {
    fix s t p q
    {
      fix s t p
      have "((\<rightarrow>\<^sub>\<beta>) \<squnion> (\<rightarrow>\<^sub>\<beta>)\<inverse>)\<^sup>*\<^sup>* s t \<Longrightarrow> ((\<rightarrow>\<^sub>\<beta>) \<squnion> (\<rightarrow>\<^sub>\<beta>)\<inverse>)\<^sup>*\<^sup>* (s \<cdot> p) (t \<cdot> p)"
        by (induct set: rtranclp) 
           (blast intro: rtranclp.rtrancl_into_rtrancl)+
    }
    moreover
    {
      fix s t p
      have "((\<rightarrow>\<^sub>\<beta>) \<squnion> (\<rightarrow>\<^sub>\<beta>)\<inverse>)\<^sup>*\<^sup>* s t \<Longrightarrow> ((\<rightarrow>\<^sub>\<beta>) \<squnion> (\<rightarrow>\<^sub>\<beta>)\<inverse>)\<^sup>*\<^sup>* (p \<cdot> s) (p \<cdot> t)"
        by (induct set: rtranclp) 
           (blast intro: rtranclp.rtrancl_into_rtrancl)+
    }
    ultimately have 
      "((\<rightarrow>\<^sub>\<beta>) \<squnion> (\<rightarrow>\<^sub>\<beta>)\<inverse>)\<^sup>*\<^sup>* s t \<Longrightarrow>
         ((\<rightarrow>\<^sub>\<beta>) \<squnion> (\<rightarrow>\<^sub>\<beta>)\<inverse>)\<^sup>*\<^sup>* p q \<Longrightarrow> 
         ((\<rightarrow>\<^sub>\<beta>) \<squnion> (\<rightarrow>\<^sub>\<beta>)\<inverse>)\<^sup>*\<^sup>* (s \<cdot> p) (t \<cdot> q)"
      by (meson rtranclp_trans)
  } note \<ddagger> = this
  show "p \<approx>\<^sub>\<beta> q \<Longrightarrow> ((\<rightarrow>\<^sub>\<beta>) \<squnion> (\<rightarrow>\<^sub>\<beta>)\<inverse>)\<^sup>*\<^sup>* p q"
    by (induct set: beta_equiv,
          blast+,
          blast intro: \<dagger>,
          metis 
            converse_join 
            conversep_conversep 
            rtranclp_converseD 
            sup_commute,
          blast intro: \<ddagger>,
          auto)
next
  show "((\<rightarrow>\<^sub>\<beta>) \<squnion> (\<rightarrow>\<^sub>\<beta>)\<inverse>)\<^sup>*\<^sup>* p q \<Longrightarrow> p \<approx>\<^sub>\<beta> q"
  proof (induct set: rtranclp)
    show "p \<approx>\<^sub>\<beta> p" by simp
  next
    fix x y
    assume "p \<approx>\<^sub>\<beta> x"
    moreover
    assume "((\<rightarrow>\<^sub>\<beta>) \<squnion> (\<rightarrow>\<^sub>\<beta>)\<inverse>) x y"
    hence "x \<rightarrow>\<^sub>\<beta> y \<or> y \<rightarrow>\<^sub>\<beta> x" by auto
    moreover
    {
      fix p q
      have "p \<rightarrow>\<^sub>\<beta> q \<Longrightarrow> p \<approx>\<^sub>\<beta> q"
        by (induct set: beta, auto)
    }
    ultimately show "p \<approx>\<^sub>\<beta> y"
      by (meson beta_equiv.symm beta_equiv.trans) 
  qed
qed


end
