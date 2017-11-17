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

type_synonym system = "constraint set"

(* (a) *)
(* functions lifted to msg list get a postfix l
functions lifted to constraints get a postfix c
functions lifted to systems get a postfix s *)
definition sapplyl::"subst_msg \<Rightarrow> msg list \<Rightarrow> msg list" where
"sapplyl s l = map (sapply_msg s) l"
definition sapplyc:: "subst_msg \<Rightarrow> constraint \<Rightarrow> constraint" where
"sapplyc s c = (case c of  a|m}t \<Rightarrow> (sapplyl s a)|(sapplyl s m)}( sapply_msg s t))"
definition sapplys:: "subst_msg \<Rightarrow> system \<Rightarrow> system" where
"sapplys s cs = image (sapplyc s) cs"


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
"fvs cs = (\<Union>c \<in> cs. fvc c)"

(* (b) *)
(* solution set *)
definition solved:: "constraint \<Rightarrow> bool" where
"solved c = (case c of (m|a}t) \<Rightarrow> ((set m \<union> set a) \<turnstile> t))"

definition sol:: "system \<Rightarrow> subst_msg set" where
"sol cs = {s. (\<forall> c \<in> cs. solved (sapplyc s c))}"

lemma solE: "s \<in> sol cs \<Longrightarrow> ((\<And>c. c \<in> cs \<Longrightarrow> solved (sapplyc s c)) \<Longrightarrow> P) \<Longrightarrow>P"
  by(auto simp add:sol_def)

lemma solI: "(\<And>c. c \<in> cs \<Longrightarrow> solved (sapplyc s c)) \<Longrightarrow> s \<in> sol cs"
  by(auto simp add:sol_def)

(* lemmas *)

lemma sol_concat: "sol(cs \<union> cs') = sol(cs) \<inter> sol(cs')"
proof((rule equalityI;rule subsetI),rule IntI)
qed(auto simp add:sol_def)

lemma "sol_scomp": "t \<in> sol(sapplys s cs) \<Longrightarrow> (scomp_msg t s) \<in> sol(cs)"
proof(rule solI, erule solE)
  fix c
  assume w:"c \<in> cs"
  assume x:"\<And>d. d \<in> (sapplys s cs) \<Longrightarrow> solved (sapplyc t d)"
  have "solved (sapplyc (scomp_msg t s) c) = solved (sapplyc t (sapplyc s c))" (is "_ = solved (sapplyc t (?d))")
    by(simp add: sapplyc_scomp)
  moreover have "?d \<in> (sapplys s cs)" by(simp add:w sapplys_def)
  ultimately show "solved (sapplyc (scomp_msg t s) c)"
    by(simp add:x)
qed

(* (c) *)
inductive rer1 :: "constraint \<Rightarrow> subst_msg \<Rightarrow> system \<Rightarrow> bool "
("(_)/\<leadsto>1[_]/ (_)" [64,64,64]63)    where
rer1_unify: "t\<noteq>Variable _ \<Longrightarrow> u \<in> set m \<union> set a \<Longrightarrow> unify_msg [(t,u)] = Some s \<Longrightarrow> (a|m}t)\<leadsto>1[s] {}"
| rer1_comp_hash:"(a|m} (Hash t)) \<leadsto>1[(%x.(Variable x))] {(a|m} t)}"
| rer1_comp_concat:"(a|m} (Concat t u)) \<leadsto>1[(%x.(Variable x))] {a|m} t, a|m} u}"
| rer1_comp_sym_encrypt:"(a|m} (Sym_encrypt t u)) \<leadsto>1[(%x.(Variable x))] {a|m} t, a|m} u}"
| rer1_comp_pub_encrypt:"(a|m} (Pub_encrypt t u)) \<leadsto>1[(%x.(Variable x))] {a|m} t, a|m} u}"
| rer1_comp_sign:"(a|m} (Sign t (Const ''intruder''))) \<leadsto>1[(%x.(Variable x))] {a|m} t}"
| rer1_proj: "((Concat u v)#a) | m } t \<leadsto>1[(%x. Variable x)] {((u#v#a) | ((Concat u v)#m) } t)}"
| rer1_sdec: "((Sym_encrypt u k)#a) | m } t \<leadsto>1[(%x. Variable x)]
 {  ((u#a) | ((Sym_encrypt u k)#m) } t) ,
    (a | ((Sym_encrypt u k)#m) } k)     }"
| rer1_adec: "((Pub_encrypt u (Variable ''intruder''))#a) | m } t \<leadsto>1[(%x. Variable x)]
 { ((u#a) | ((Pub_encrypt u (Variable ''intruder''))#m) } t) }"
| rer1_ksub: "x=Pub_encrypt u (Variable agent) \<Longrightarrow>
s=(%v. Variable (if v=agent then ''intruder'' else v)) \<Longrightarrow>
(x#a) | m } t  \<leadsto>1[s] { sapplyc s ((x#a) | m } t) }"

inductive rer :: "system \<Rightarrow> subst_msg \<Rightarrow> system \<Rightarrow> bool " ("(_)/\<leadsto>[_]/ _ " [73,73,73]72) where
"c \<leadsto>1[s] cs \<Longrightarrow> (insert c cs') \<leadsto>[s] (cs \<union> (sapplys s cs'))"

definition rer_star :: "system \<Rightarrow>subst_msg \<Rightarrow> system \<Rightarrow> bool" ("(_)/\<leadsto>*[_]/ _ " [73,73,73]72) where
"cs \<leadsto>*[s] cs' = ((cs, cs') \<in> (rtrancl { (x, y) . (x \<leadsto>[s] y) }))"

end