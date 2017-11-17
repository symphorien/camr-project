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

(* assignment 7 *)
datatype constraint =
Constraint "msg list " "msg list " "msg " ( "((2_/|_)/} _) " [67,67,67]66)
(* elements go from the first list to the second.
they are popped from the head of the first list and are push to the top
of the second one *)

type_synonym system = "constraint list"

(* (a) *)
(* functions lifted to msg list get a postfix l
functions lifted to constraints get a postfix c
functions lifted to systems get a postfix s *)
definition sapplyl::"subst_msg \<Rightarrow> msg list \<Rightarrow> msg list" where
"sapplyl s l = map (sapply_msg s) l"
definition sapplyc:: "subst_msg \<Rightarrow> constraint \<Rightarrow> constraint" where
"sapplyc s c = (case c of  a|m}t \<Rightarrow> (sapplyl s a)|(sapplyl s m)}( sapply_msg s t))"
definition sapplys:: "subst_msg \<Rightarrow> system \<Rightarrow> system" where
"sapplys s cs = map (sapplyc s) cs"

lemma sapplyc_scomp:"sapplyc (scomp_msg t s) c = sapplyc t (sapplyc s (c))"
  apply(cases c)
  apply(auto simp add:sapplyc_def sapplyl_def)
    apply(simp_all add:sapply_msg_scomp_msg)
  done

definition fvl:: "msg list \<Rightarrow> var set" where
"fvl l = (\<Union>m \<in> set l. fv_msg m)"
definition fvc:: "constraint \<Rightarrow> var set" where
"fvc c = (case c of a|m}t \<Rightarrow> (fvl a) \<union> (fvl m) \<union> (fv_msg t))"
definition fvs:: "system \<Rightarrow> var set" where
"fvs cs = (\<Union>c \<in> set cs. fvc c)"

(* (b) *)
(* solution set *)
definition solved:: "constraint \<Rightarrow> bool" where
"solved c = (case c of (m|a}t) \<Rightarrow> ((set m \<union> set a) \<turnstile> t))"

definition sol:: "system \<Rightarrow> subst_msg set" where
"sol cs = {s. (\<forall> c \<in> set cs. solved (sapplyc s c))}"

lemma solE: "s \<in> sol cs \<Longrightarrow> ((\<And>c. c \<in> set cs \<Longrightarrow> solved (sapplyc s c)) \<Longrightarrow> P) \<Longrightarrow>P"
  by(auto simp add:sol_def)

lemma solI: "(\<And>c. c \<in> set cs \<Longrightarrow> solved (sapplyc s c)) \<Longrightarrow> s \<in> sol cs"
  by(auto simp add:sol_def)

(* lemmas *)

lemma sol_concat: "sol(cs @ cs') = sol(cs) \<inter> sol(cs')"
proof((rule equalityI;rule subsetI),rule IntI)
qed(auto simp add:sol_def)

lemma "sol_scomp": "t \<in> sol(sapplys s cs) \<Longrightarrow> (scomp_msg t s) \<in> sol(cs)"
proof(rule solI, erule solE)
  fix c
  assume w:"c \<in> set cs"
  assume x:"\<And>d. d \<in> set (sapplys s cs) \<Longrightarrow> solved (sapplyc t d)"
  have "solved (sapplyc (scomp_msg t s) c) = solved (sapplyc t (sapplyc s c))" (is "_ = solved (sapplyc t (?d))")
    by(simp add: sapplyc_scomp)
  moreover have "?d \<in> set (sapplys s cs)" by(simp add:w sapplys_def)
  ultimately show "solved (sapplyc (scomp_msg t s) c)"
    by(simp add:x)
qed

end