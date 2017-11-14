theory Deduction imports Main Term begin

(* assignment 6 *)
(* (a) *)

inductive deduce::  "msg set\<Rightarrow>msg\<Rightarrow>bool"   (infix "\<turnstile>" 72)
  for T :: "msg set" where
deduce_axiom: "u \<in> T \<Longrightarrow> deduce T u"
| deduce_comp_hash: "deduce T x \<Longrightarrow> deduce T (Hash x)"
| deduce_comp_concat: "deduce T x \<Longrightarrow> deduce T y \<Longrightarrow> deduce T (Concat x y)"
| deduce_comp_sym_encrypt: "deduce T x \<Longrightarrow> deduce T y \<Longrightarrow> deduce T (Sym_encrypt x y)"
| deduce_comp_pub_encrypt: "deduce T x \<Longrightarrow> deduce T y \<Longrightarrow> deduce T (Pub_encrypt x y)"
| deduce_comp_sign: "deduce T x \<Longrightarrow> deduce T (Sign x (Const ''intruder''))"
| deduce_proj1: "deduce T (Concat x y) \<Longrightarrow> deduce T x"
| deduce_proj2: "deduce T (Concat x y) \<Longrightarrow> deduce T y"
| deduce_sym_decrypt: "deduce T (Sym_encrypt x y) \<Longrightarrow> deduce T y \<Longrightarrow> deduce T x"
| deduce_pub_decrypt: "deduce T (Pub_encrypt x (Const ''intruder'')) \<Longrightarrow> deduce T x"

(* testing *)
lemma "deduce {Sym_encrypt x y, y} x" by(auto intro:deduce.intros)
lemma "deduce {m, n} (Hash (Concat m n))" by(auto intro:deduce.intros)
lemma "deduce {Sym_encrypt m k, Pub_encrypt k (Const ''intruder'')} (Concat m (Sign m (Const ''intruder'')))" (is "deduce ?T ?g")
proof-
  have "deduce ?T k" by(auto intro:deduce.intros)
  then show "deduce ?T ?g" by(auto intro:deduce.intros)
qed

(* (b) *) 
lemma deduce_weaken:
  assumes "G \<turnstile> t" and "G \<subseteq> H"
  shows "H \<turnstile> t"
  using assms
proof(induction rule:deduce.induct)
qed(auto intro:deduce.intros)

lemma deduce_cut:
  assumes "(insert t H) \<turnstile> u" and "H \<turnstile> t"
  shows "H \<turnstile> u"
  using assms
proof(induction rule:deduce.induct)
qed(auto intro:deduce.intros)

end