theory Snippets
  imports "~~/src/HOL/Library/LaTeXsugar"
          "../DeBruijn"
begin

text \<open>
\DefineSnippet{refl axiom}{
@{thm[mode=Axiom] refl} {\sc refl}
}%EndSnippet
\<close>

text \<open>
\DefineSnippet{graph_reachable}{
\<open>(R \<squnion> R\<inverse>)\<^sup>*\<^sup>* x y\<close>
}%EndSnippet

\DefineSnippet{graph_equiv}{
\<open>x \<approx>\<^sub>R y\<close>
}%EndSnippet

\DefineSnippet{Church_Rosser_def_rhs}{
@{thm (rhs) Church_Rosser_def}
}%EndSnippet

\DefineSnippet{Church_Rosser_def_lhs}{
@{thm (lhs) Church_Rosser_def}
}%EndSnippet

\DefineSnippet{beta_equiv_refl}{
@{thm[mode=Axiom] beta_equiv.refl}
}%EndSnippet

\DefineSnippet{beta_equiv_subst}{
@{thm[mode=Axiom] beta_equiv.subst}
}%EndSnippet

\DefineSnippet{beta_equiv_abs}{
@{thm[mode=Rule] beta_equiv.abs}
}%EndSnippet

\DefineSnippet{beta_equiv_symm}{
@{thm[mode=Rule] beta_equiv.symm}
}%EndSnippet

\DefineSnippet{beta_equiv_app}{
@{thm[mode=Rule] beta_equiv.app}
}%EndSnippet

\DefineSnippet{beta_beta}{
@{thm[mode=Axiom] beta.beta}
}%EndSnippet

\DefineSnippet{beta_appL}{
@{thm[mode=Rule] beta.appL}
}%EndSnippet

\DefineSnippet{beta_appR}{
@{thm[mode=Rule] beta.appR}
}%EndSnippet

\DefineSnippet{beta_abs}{
@{thm[mode=Rule] beta.abs}
}%EndSnippet

\DefineSnippet{beta_beta_no_rule}{
@{thm beta.beta}
}%EndSnippet

\DefineSnippet{beta_equiv_alt_def}{
@{thm beta_equiv_alt_def}
}%EndSnippet

\DefineSnippet{Church_Rosser_confluent}{
@{thm Church_Rosser_confluent}
}%EndSnippet

\DefineSnippet{beta_equiv}{
\<^term>\<open>p \<approx>\<^sub>\<beta> q\<close>
}%EndSnippet

\DefineSnippet{confluent_diamond}{
\<open>confluent R = diamond (R\<^sup>*)\<close>
}%EndSnippet

\DefineSnippet{diamond_confluent}{
@{thm diamond_confluent}
}%EndSnippet

\DefineSnippet{par_beta_var}{
@{thm[mode=Axiom] par_beta.var}
}%EndSnippet

\DefineSnippet{par_beta_abs}{
@{thm[mode=Rule] par_beta.abs}
}%EndSnippet

\DefineSnippet{par_beta_beta}{
@{thm[mode=Rule] par_beta.beta}
}%EndSnippet

\DefineSnippet{par_beta_app}{
@{thm[mode=Rule] par_beta.app}
}%EndSnippet

\DefineSnippet{beta_implies_par_beta}{
@{thm beta_implies_par_beta}
}%EndSnippet

\DefineSnippet{par_beta_implies_transitive_beta}{
@{thm par_beta_implies_transitive_beta}
}%EndSnippet

\DefineSnippet{diamond_par_beta}{
@{thm diamond_par_beta}
}%EndSnippet

\DefineSnippet{par_beta_confluent}{
@{thm par_beta_confluent}
}%EndSnippet

\DefineSnippet{beta_confluent}{
@{thm beta_confluent}
}%EndSnippet
\<close>


text_raw \<open>\DefineSnippet{db_Syntax}{\<close>
datatype dB =
    Variable nat ("\<langle>_\<rangle>" [100] 100)
  | Application dB dB (infixl "\<cdot>" 200)
  | Abstraction dB ("\<^bold>\<lambda>")
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{lifting_def}{\<close>
primrec
  lift :: "dB \<Rightarrow> nat \<Rightarrow> dB"
where
    "lift (\<langle>i\<rangle>) k = (if i < k then \<langle>i\<rangle> else \<langle>(i + 1)\<rangle>)"
  | "lift (s \<cdot> t) k = lift s k \<cdot> lift t k"
  | "lift (\<^bold>\<lambda> s) k = \<^bold>\<lambda> (lift s (k + 1))"
text_raw \<open>}%EndSnippet\<close>

no_notation subst ("_[_ '\<^bold>\<mapsto> _]" [300, 0, 0] 300)

text_raw \<open>\DefineSnippet{substitution_def}{\<close>
primrec
  subst :: "dB \<Rightarrow> nat \<Rightarrow> dB \<Rightarrow> dB"  
  ("_[_ '\<^bold>\<mapsto> _]" [300, 0, 0] 300)
  where
    subst_Var: "(\<langle>i\<rangle>)[k \<^bold>\<mapsto> s] =
      (if k < i then \<langle>(i - 1)\<rangle> else if i = k then s else \<langle>i\<rangle>)"
  | subst_App: "(t \<cdot> u)[k \<^bold>\<mapsto> s] = t[k \<^bold>\<mapsto> s] \<cdot> u[k \<^bold>\<mapsto> s]"
  | subst_Abs: "(\<^bold>\<lambda> t)[k \<^bold>\<mapsto> s] = \<^bold>\<lambda> (t [k + 1 \<^bold>\<mapsto> lift s 0])"
text_raw \<open>}%EndSnippet\<close>


end
