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

lemma solvedI: "(set a \<union> set m) \<turnstile> t \<Longrightarrow> solved (a|m}t)"
  by(auto simp add:solved_def)

lemma solvedE: "solved (a|m}t) \<Longrightarrow> ((set a \<union> set m) \<turnstile> t \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add:solved_def)

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

(* (c) *)
inductive rer1 :: "constraint \<Rightarrow> subst_msg \<Rightarrow> system \<Rightarrow> bool "
("(_)/\<leadsto>1[_]/ (_)" [64,64,64]63)    where
rer1_unify: "(\<And> z. t\<noteq>Variable z) \<Longrightarrow> u \<in> set m \<union> set a \<Longrightarrow> unify_msg [(t,u)] = Some s \<Longrightarrow> (a|m}t)\<leadsto>1[s] []"
| rer1_comp_hash:"(a|m} (Hash t)) \<leadsto>1[Variable] [(a|m} t)]"
| rer1_comp_concat:"(a|m} (Concat t u)) \<leadsto>1[Variable] [ a|m} t, a|m}u ]"
| rer1_comp_sym_encrypt:"(a|m} (Sym_encrypt t u)) \<leadsto>1[Variable] [ a|m}t, a|m}u ]"
| rer1_comp_pub_encrypt:"(a|m} (Pub_encrypt t u)) \<leadsto>1[Variable] [ a|m}t, a|m}u ]"
| rer1_comp_sign:"(a|m} (Sign t (Const ''intruder''))) \<leadsto>1[Variable] [a|m} t]"
| rer1_proj: "x=Concat u v \<Longrightarrow> (head@x#tail) | m } t \<leadsto>1[Variable] [ (u#v#head@tail) | (x#m) } t ]"
| rer1_sdec: "x=Sym_encrypt u k \<Longrightarrow> (head@x#tail) | m } t \<leadsto>1[Variable]
 [  ((u#head@tail) | (x#m) } t) ,
    ((head@tail) | (x#m) } k)     ]"
| rer1_adec: "x=Pub_encrypt u (Variable ''intruder'') \<Longrightarrow> (head@x#tail) | m } t \<leadsto>1[Variable]
 [ ((u#head@tail) | (x#m) } t) ]"
| rer1_ksub: "Pub_encrypt u (Variable agent) \<in> set a \<Longrightarrow>
s=(%v. Variable (if v=agent then ''intruder'' else v)) \<Longrightarrow>
a | m } t  \<leadsto>1[s] [ sapplyc s (a|m}t) ]"

inductive rer :: "system \<Rightarrow> subst_msg \<Rightarrow> system \<Rightarrow> bool " ("(_)/\<leadsto>[_]/ _ " [73,73,73]72) where
"c \<leadsto>1[s] cs \<Longrightarrow> (head@c#tail) \<leadsto>[s] (cs @ (sapplys s (head@tail)))"

inductive rer_star :: "system \<Rightarrow> subst_msg \<Rightarrow> system \<Rightarrow> bool" ("(_)/\<leadsto>*[_]/ _ " [73,73,73]72) where
rer_star_id: "cs \<leadsto>*[Variable] cs"
| rer_star_step: "cs \<leadsto>[s] cs'' \<Longrightarrow> cs'' \<leadsto>*[t] cs' \<Longrightarrow> cs \<leadsto>*[scomp_msg t s] cs'"

(* (d) *)
inductive simplec:: "constraint \<Rightarrow> bool" where
"fvl a = {} \<Longrightarrow> fvl m = {} \<Longrightarrow> simplec (a|m}t)"

definition simples:: "system \<Rightarrow> bool" where
"simples cs = (\<forall> c \<in> set cs. simplec c)"

inductive is_red:: "system \<Rightarrow> subst_msg \<Rightarrow> bool" where
"cs \<leadsto>*[s] cs' \<Longrightarrow> simples cs' \<Longrightarrow> t \<in> sol(cs') \<Longrightarrow> is_red cs (scomp_msg t s)"

definition red:: "system \<Rightarrow> subst_msg set" where
"red cs = {t . is_red cs t}"

lemma redE: "x \<in> red cs \<Longrightarrow> (is_red cs x \<Longrightarrow> P) \<Longrightarrow> P"
  by(simp add:red_def)
 
lemma is_redE: "is_red cs u \<Longrightarrow>
(\<And>t s cs'. u=scomp_msg t s \<Longrightarrow> cs \<leadsto>*[s] cs' \<Longrightarrow> simples cs' \<Longrightarrow> t \<in> sol(cs')  \<Longrightarrow> P)
\<Longrightarrow> P"
proof(cases rule:is_red.cases)
qed(simp_all)

(* Assignment 8 *)
lemma sol_rer1:"c \<leadsto>1[s] cs \<Longrightarrow> v \<in> sol cs \<Longrightarrow> (scomp_msg v s) \<in> sol [c]"
proof(induction c s cs arbitrary: v rule:rer1.induct)
case (rer1_unify t u m a s v)
  then show ?case
  proof -
    let ?target = "scomp_msg v s"
assume nvar:"\<And>z. t \<noteq> Variable z" and app:"u \<in> set m \<union> set a"
      and unif:"unify_msg [(t, u)] = Some s" and sol:"v \<in> sol []"
  from unif have "unifiess_msg s [(t, u)]" by(rule unify_msg_return)
  then have "sapply_msg s t = sapply_msg s u"
    by(auto elim!:unifiess_msgE unifies_msgE)
  then have eq:"sapply_msg ?target t = sapply_msg ?target u" by(simp add:sapply_msg_scomp_msg)
  have "u \<in> set m \<union> set a \<Longrightarrow> solved (sapplyl ?target a| sapplyl ?target m}sapply_msg ?target u)"
  proof(erule UnE; (rule solvedI, rule deduce_axiom))
  qed(auto simp add:sapplyl_def)
  from app and this have "solved (sapplyl ?target a| sapplyl ?target m}sapply_msg ?target t)" by(simp add:eq)
  then have "solved (sapplyc ?target (a|m}t))" by(simp add:sapplyc_def)
  then show "?target \<in> sol [a|m} t ]" by(auto intro:solI)
qed
next
case (rer1_comp_hash a m t)
  then show ?case sorry
next
  case (rer1_comp_concat a m t u)
  then show ?case sorry
next
  case (rer1_comp_sym_encrypt a m t u)
  then show ?case sorry
next
  case (rer1_comp_pub_encrypt a m t u)
  then show ?case sorry
next
  case (rer1_comp_sign a m t)
  then show ?case sorry
next
  case (rer1_proj x u v head tail m t)
  then show ?case sorry
next
  case (rer1_sdec x u k head tail m t)
  show ?case
  proof -
    from rer1_sdec have xdef:"x = Sym_encrypt u k"
      and sol:"v \<in> sol [(u # head @ tail)|(x # m)} t , (head @ tail)|(x # m)} k ]" (is "v \<in> sol [?c1, ?c2]")
      .
    let ?T = "set (map (sapply_msg v) (x#m@head@tail))"

    have "sapply_msg v x \<in> ?T" by simp
    then have "deduce ?T (sapply_msg v x)" by(rule deduce_axiom)
    moreover have "sapply_msg v x = Sym_encrypt (sapply_msg v u) (sapply_msg v k)"
      by(simp add:sapply_msg_simps xdef)
    ultimately have sdec1:"deduce ?T (Sym_encrypt (sapply_msg v u) (sapply_msg v k))"
      by simp

    from sol have "solved (sapplyc v ?c2)" by(auto elim:solE)
    then have "(set (sapplyl v (head@tail)) \<union> set (sapplyl v (x#m))) \<turnstile> (sapply_msg v k)"
      by(auto simp add:sapplyc_def elim:solvedE)
    moreover have "(set (sapplyl v (head@tail)) \<union> set (sapplyl v (x#m))) = ?T"
      by(simp add:sapplyl_def Un_commute)
    ultimately have sdec2:"?T \<turnstile> (sapply_msg v k)"
      by(auto simp add:sapplyl_def)

    from sdec1 and sdec2 have cut1:"?T \<turnstile> (sapply_msg v u)" by(rule deduce_sym_decrypt)

    let ?rewrite = "insert (sapply_msg v u) ?T" 
    from sol have "solved (sapplyc v ?c1)" by(auto elim:solE)
    then have "(set (sapplyl v (u#head@tail)) \<union> set (sapplyl v (x#m))) \<turnstile> (sapply_msg v t)"
      by(auto simp add:sapplyc_def elim:solvedE)
    moreover have "(set (sapplyl v (u#head@tail)) \<union> set (sapplyl v (x#m))) = ?rewrite"
      by(simp add:sapplyl_def Un_commute)
    ultimately have cut2:"?rewrite \<turnstile> (sapply_msg v t)"
      by(auto simp add:sapplyl_def)

    let ?a="(head @ x # tail)"

    from cut2 and cut1 have "?T \<turnstile> (sapply_msg v t)" by(rule deduce_cut)    
    then have "solved (sapplyc v (?a|m}t))"
      by(auto simp add:sapplyc_def Un_commute sapplyl_def intro!:solI solvedI)
    then have "v \<in> sol [?a|m}t]" by(auto intro:solI)
    then show "scomp_msg v Variable \<in> sol [(head @ x # tail)|m} t ]" by(simp)
  qed
next
  case (rer1_adec x u head tail m t)
  then show ?case sorry
next
  case (rer1_ksub u agent a s m t)
  then show ?case sorry
qed


end