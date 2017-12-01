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

lemma sapplyl_Variable[simp]: "sapplyl Variable x = x"
proof(induction x)
  case Nil
  then show ?case by(simp add:sapplyl_def sapply_msg_simps)
next
  case (Cons a x)
  then show ?case by(simp add:sapplyl_def sapply_msg_simps)
qed

lemma sapplyc_Variablei[simp]: "sapplyc Variable x = x"
  by(cases x)(simp add:sapplyc_def sapply_msg_simps)

lemma sapplys_Variable[simp]: "sapplys Variable x = x"
proof(induction x)
  case Nil
then show ?case by(simp add:sapplys_def)
next
  case (Cons a x)
  then show ?case by(simp add:sapplys_def)
qed
  

fun fvl:: "msg list \<Rightarrow> var set" where
"fvl l = (\<Union>m \<in> set l. fv_msg m)"
fun fvc:: "constraint \<Rightarrow> var set" where
"fvc c = (case c of a|m}t \<Rightarrow> (fvl a) \<union> (fvl m) \<union> (fv_msg t))"
fun fvs:: "system \<Rightarrow> var set" where
"fvs cs = (\<Union>c \<in> set cs. fvc c)"

lemma fv_sapplyl_sdom_svran: "fvl (sapplyl s l) \<subseteq> ((fvl l) - sdom_msg s) \<union> (svran_msg s)" (is "?lhs \<subseteq> ?rhs")
proof(induction l)
  case Nil
  then show ?case by(simp add:sapplyl_def fv_sapply_sdom_svran_msg)
next
  case (Cons a as)
  have "fv_msg (sapply_msg s a) \<subseteq> ((fv_msg (a)) - sdom_msg s) \<union> (svran_msg s)"
    by(rule fv_sapply_sdom_svran_msg)
  then have "fv_msg (sapply_msg s a) \<subseteq> ((fvl (a#as)) - sdom_msg s) \<union> (svran_msg s)"
    by(auto)
  moreover have "fvl (sapplyl s as) \<subseteq> ((fvl (as)) - sdom_msg s) \<union> (svran_msg s)"
    by(rule Cons)
  then have "fvl (sapplyl s as) \<subseteq> ((fvl (a#as)) - sdom_msg s) \<union> (svran_msg s)" by auto
  moreover have "fvl (sapplyl s (a#as)) = fv_msg (sapply_msg s a) \<union> fvl (sapplyl s as)"
    by(simp add:sapplyl_def)
  ultimately show "fvl (sapplyl s (a#as)) \<subseteq> ((fvl (a#as)) - sdom_msg s) \<union> (svran_msg s)"
    by(simp add:sapplyl_def)
qed

lemma fv_sapplyc_sdom_svran: "fvc (sapplyc s c) \<subseteq> ((fvc c) - sdom_msg s) \<union> (svran_msg s)" (is "?lhs \<subseteq> ?rhs")
proof(cases c)
  case (Constraint a m t)
  from fv_sapply_sdom_svran_msg[of s t] have "fv_msg (sapply_msg s t) \<subseteq> ?rhs"
    by(auto simp add:Constraint Un_commute Un_assoc insert_commute)
  moreover from fv_sapplyl_sdom_svran[of s a] have "fvl (sapplyl s a) \<subseteq> ?rhs"
    by(auto simp add:Constraint Un_commute Un_assoc insert_commute)
  moreover from fv_sapplyl_sdom_svran[of s m] have "fvl (sapplyl s m) \<subseteq> ?rhs"
    by(auto simp add:Constraint Un_commute Un_assoc insert_commute)
  ultimately show ?thesis
    by(simp add:sapplyc_def Constraint)
qed

lemma fv_sapplys_sdom_svran: "fvs (sapplys s cs) \<subseteq> ((fvs cs) - sdom_msg s) \<union> (svran_msg s)"
proof(induction cs)
  case Nil
then show ?case by(simp add:sapplys_def fv_sapplyc_sdom_svran)
next
  case (Cons a as)
  from fv_sapplyc_sdom_svran[of s a] have "fvc (sapplyc s a) \<subseteq> ((fvs (a#as)) - sdom_msg s) \<union> (svran_msg s)"
    by(auto simp add:Cons Un_commute Un_assoc insert_commute)
  moreover from Cons have "fvs (sapplys s as) \<subseteq> ((fvs (a#as)) - sdom_msg s) \<union> (svran_msg s)"
    by(auto simp add:Cons Un_commute Un_assoc insert_commute)
  ultimately show ?case by(auto simp add:sapplys_def Un_commute Un_assoc insert_commute)
qed

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
| rer1_adec: "x=Pub_encrypt u (Const ''intruder'') \<Longrightarrow> (head@x#tail) | m } t \<leadsto>1[Variable]
 [ ((u#head@tail) | (x#m) } t) ]"
| rer1_ksub: "Pub_encrypt u (Variable agent) \<in> set a \<Longrightarrow>
s=(Variable (agent:=Const ''intruder'')) \<Longrightarrow>
a|m}t  \<leadsto>1[s] [ sapplyc s (a|m}t) ]"

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
  case (rer1_proj x u u' head tail m t)
  show ?case
  proof -
    from rer1_proj have xdef:"x = Concat u u'"
      and sol:"v \<in> sol [(u # u' # head @ tail)|(x # m)} t ]"
          (is "v \<in> sol [?c]") .
    let ?T = "set (map (sapply_msg v) (x#m@head@tail))"

    from sol have "solved (sapplyc v ?c)" by(auto elim:solE)
    then have cut1:"(insert (sapply_msg v u) (insert (sapply_msg v u') ?T)) \<turnstile> (sapply_msg v t)"
      by(auto simp add:sapplyl_def sapplyc_def elim!: solvedE)(simp only:Un_commute Un_assoc insert_commute)

    have pair:"(insert (sapply_msg v u') ?T) \<turnstile> (sapply_msg v x)" (is "?T' \<turnstile> _")
      by(rule deduce_axiom)(simp add:sapply_msg_simps xdef)
    then have "?T' \<turnstile> (sapply_msg v u)" by(auto intro:deduce_proj1 simp add:sapply_msg_simps xdef)
    from cut1 and this have cut2:"?T' \<turnstile> (sapply_msg v t)" by(rule deduce_cut)
    have "?T \<turnstile> (sapply_msg v x)"
      by(rule deduce_axiom)(simp add:sapply_msg_simps xdef)
    then have "?T \<turnstile> (sapply_msg v u')" by(auto intro:deduce_proj2 simp add:sapply_msg_simps xdef)
    from cut2 and this have "?T \<turnstile> (sapply_msg v t)" by(rule deduce_cut)
    then show "scomp_msg v Variable \<in> sol [(head @ x # tail)|m} t ]"
      by(auto simp add:sapplyc_def Un_commute sapplyl_def intro!:solI solvedI)
  qed
next
  case (rer1_sdec x u k head tail m t)
  show ?case
  proof -
    from rer1_sdec have xdef:"x = Sym_encrypt u k"
      and sol:"v \<in> sol [(u # head @ tail)|(x # m)} t , (head @ tail)|(x # m)} k ]"
          (is "v \<in> sol [?c1, ?c2]") .
    let ?T = "set (map (sapply_msg v) (x#m@head@tail))"

    have "sapply_msg v x \<in> ?T" by simp
    then have "deduce ?T (sapply_msg v x)" by(rule deduce_axiom)
    then have sdec1:"deduce ?T (Sym_encrypt (sapply_msg v u) (sapply_msg v k))"
      by(simp add:sapply_msg_simps xdef)

    from sol have "solved (sapplyc v ?c2)" by(auto elim:solE)
    then have sdec2:"?T \<turnstile> (sapply_msg v k)"
      by(auto simp add:sapplyl_def sapplyc_def Un_commute elim!: solvedE)

    from sdec1 and sdec2 have cut1:"?T \<turnstile> (sapply_msg v u)" by(rule deduce_sym_decrypt)

    from sol have "solved (sapplyc v ?c1)" by(auto elim:solE)
    then have cut2:"insert (sapply_msg v u) ?T \<turnstile> (sapply_msg v t)"
      by(auto simp add:sapplyl_def sapplyc_def Un_commute elim:solvedE)

    from cut2 and cut1 have "?T \<turnstile> (sapply_msg v t)" by(rule deduce_cut)    
    then show "scomp_msg v Variable \<in> sol [(head @ x # tail)|m} t ]"
      by(auto simp add:sapplyc_def Un_commute sapplyl_def intro!:solI solvedI)
  qed
next
  case (rer1_adec x u head tail m t)
  show ?case
  proof -
    from rer1_adec have xdef:"x = Pub_encrypt u (Const ''intruder'')" (is "x = Pub_encrypt u ?i")
      and sol:"v \<in> sol [(u # head @ tail)|(x # m)} t ]"
          (is "v \<in> sol [?c]").
    let ?T = "set (map (sapply_msg v) (x#m@head@tail))"

    from sol have "solved (sapplyc v ?c)" by(auto elim:solE)
    then have cut1:"(insert (sapply_msg v u) ?T) \<turnstile> (sapply_msg v t)"
      by(auto simp add:sapplyl_def sapplyc_def elim!: solvedE)(simp only:Un_commute Un_assoc insert_commute)

    have "?T \<turnstile> (sapply_msg v x)"
      by(rule deduce_axiom)(simp add:sapply_msg_simps xdef)
    then have "?T \<turnstile> (sapply_msg v u)" by(auto intro:deduce_pub_decrypt simp add:sapply_msg_simps xdef)
    from cut1 and this have "?T \<turnstile> (sapply_msg v t)" by(rule deduce_cut)
    then show "scomp_msg v Variable \<in> sol [(head @ x # tail)|m} t ]"
      by(auto simp add:sapplyc_def Un_commute sapplyl_def intro!:solI solvedI)
  qed
next
  case (rer1_ksub u agent a s m t)
  then have "v \<in> sol (sapplys s [(a|m} t )])" by(simp add:sapplys_def)
  then show ?case by(rule sol_scomp)
qed(auto simp add:sapplyc_def sapplyl_def sapply_msg_simps elim!:solE solvedE
intro!:solI solvedI deduce_comp_hash deduce_comp_sign deduce_comp_concat
deduce_comp_pub_encrypt deduce_comp_sym_encrypt)

lemma sol_rer: "cs \<leadsto>[s] cs' \<Longrightarrow> t \<in> sol(cs') \<Longrightarrow> (scomp_msg t s) \<in> sol cs"
proof(induction cs s cs' arbitrary: t rule:rer.induct)
  case hyp:(1 c s cs head tail)
  then have "t \<in> sol cs" by(simp add:sol_concat)
  from `c\<leadsto>1[s] cs` and this have half:"scomp_msg t s \<in> sol [c]" by(rule sol_rer1)

  from hyp have "t \<in> sol (sapplys s (head@tail))" by(simp add:sol_concat)
  then have half2:"scomp_msg t s \<in> sol (head@tail)" by(auto simp add:sol_scomp)

  have "sol (head @ c # tail) = sol head \<inter> sol [c] \<inter> sol tail" 
    by(simp add:sol_concat[symmetric, of "[c]" tail] sol_concat[symmetric])
  from this and half and half2 show ?case by(simp add:sol_concat)
qed

lemma sol_rer_star: "cs \<leadsto>*[s] cs' \<Longrightarrow> simples cs' \<Longrightarrow> t \<in> sol(cs') \<Longrightarrow> (scomp_msg t s) \<in> sol cs"
proof(induction cs s cs' arbitrary: t rule:rer_star.induct)
case (rer_star_id cs)
  then show ?case by simp
next
  case (rer_star_step cs s cs'' t cs' u)
  from `simples cs'` and `u \<in> sol cs'` have "scomp_msg u t \<in> sol cs''" by(rule rer_star_step)
  from `cs \<leadsto>[s] cs''` and this have "scomp_msg (scomp_msg u t) s \<in> sol cs" by(rule sol_rer)
  then show ?case by(simp add:scomp_msg_assoc)
qed

lemma cs_sound: "red cs \<subseteq> sol cs"
  by(auto simp add:sol_rer_star elim!:redE is_redE)

(* termination -- 8b *)
fun \<theta>:: "msg \<Rightarrow> nat" where
"\<theta> (Hash x) = \<theta> x + 1"
| "\<theta> (Concat x y) = \<theta> x  + \<theta> y + 1"
| "\<theta> (Sym_encrypt x y) = \<theta> x  + \<theta> y + 1"
| "\<theta> (Pub_encrypt x y) = \<theta> x  + \<theta> y + 1"
| "\<theta> (Sign x y) = (if y= Const ''intruder'' then \<theta> x + 1 else 1)"
| "\<theta> x = 1"

fun \<chi>:: "msg \<Rightarrow> nat" where
"\<chi> (Hash x) = \<chi> x +1"
| "\<chi> (Concat x y) = (\<chi> x)*(\<chi> y) +1"
| "\<chi> (Sym_encrypt x y) = (\<chi> x) + \<theta> y + 1"
| "\<chi> (Pub_encrypt x y) = (\<chi> x) + 1"
| "\<chi> (Sign x y) = (\<chi> x) + 1"
| "\<chi> x  = 1"

fun \<chi>l :: "msg list \<Rightarrow> nat" where
"\<chi>l [] = 1" | "\<chi>l (x#tail) = (\<chi> x) * (\<chi>l tail)"

fun weight:: "constraint \<Rightarrow> nat" where
"weight (m|a}t) = (\<chi>l m)*(\<theta> t)"

fun weights:: "constraint list \<Rightarrow> nat" where
"weights [] = 0" | "weights (c#cs) = weight c + weights cs"

lemma non_zero_theta[simp]: "\<theta> x > 0"
proof(induction x rule:\<theta>.induct)
qed(simp_all)

lemma non_zero_chi[simp]: "\<chi> x > 0"
proof(induction x rule:\<chi>.induct)
qed(simp_all)

lemma non_zero_chil[simp]: "\<chi>l x > 0" by(induction x)(simp_all)
lemma non_zero_weight[simp]: "weight x > 0" by(cases x)(simp)
lemma non_zero_weights[simp]: "x \<noteq> [] \<Longrightarrow>  weights x>0" by(induction x)simp_all

lemma \<chi>l_append[simp]: "\<chi>l (a@b) = (\<chi>l a) * (\<chi>l b)"
proof(induction a;induction b)
qed simp_all

lemma rer1_fv: "c \<leadsto>1[s] cs \<Longrightarrow> fvs(cs@(sapplys s (head@tail))) \<subseteq> fvs(head@c#tail)"
proof(induction c s cs arbitrary:head tail rule:rer1.induct)
  case (rer1_unify t u m a s)
  then show ?case
  proof -
    let ?cs="head@tail"
    from `u \<in> set m \<union> set a` have x:"fv_msg u \<subseteq> fvc (a|m}t)" by(auto)
    from  `unify_msg [(t, u)] = Some s` have "svran_msg s \<subseteq> fv_eqs_msg [(t, u)]" by(rule l3_msg)
    also have "... \<subseteq> fv_msg t \<union> fv_msg u" by(auto simp add:fv_eqs_msg_def fv_msg_def)
    also have "... \<subseteq> fv_msg t \<union> fvc (a|m}t)" using x by(auto simp add:Un_commute Un_assoc insert_commute)
    finally have svinc:"svran_msg s \<subseteq> fvc (a|m}t)" by(auto)

    have "fvs (sapplys s ?cs) \<subseteq> fvs ?cs - sdom_msg s \<union> svran_msg s" by(rule fv_sapplys_sdom_svran)
    also have "... \<subseteq> fvs ?cs \<union> svran_msg s" by blast
    also have "... \<subseteq> fvs ?cs \<union> fvc (a|m}t)" using svinc by auto
    finally show ?case by(simp add:Un_commute Un_assoc insert_commute sapplys_def del:fvc.simps)
  qed
next
  case (rer1_ksub u agent a s m t)
  let ?cs="head @ a|m} t  # tail"
  have "svran_msg (Variable(agent := Const ''intruder'')) = {}"
    by(auto simp add:svran_msg_def_real sran_msg_def_real sdom_msg_def_real fv_msg_def)
  then have svran:"svran_msg s = {}"
    by(simp add:`s = Variable(agent := Const ''intruder'')`)

  have "fvs (sapplys s ?cs) \<subseteq> fvs ?cs - sdom_msg s \<union> svran_msg s" by(rule fv_sapplys_sdom_svran)
  also have "... \<subseteq> fvs ?cs - sdom_msg s" by(simp add:svran)
  finally have "fvs (sapplys s ?cs) \<subseteq> fvs ?cs" by blast

  then show ?case by(simp add:Un_commute Un_assoc insert_commute sapplys_def del:fvc.simps)
qed(auto simp add:fv_msg_def)

lemma rer1_fv2: "c \<leadsto>1[s] cs \<Longrightarrow> s \<noteq> Variable \<Longrightarrow> fvs (cs @ sapplys s (head @ tail)) \<noteq> fvs(head @ c#tail)"
proof(induction c s cs arbitrary:head tail rule:rer1.induct)
  case (rer1_unify t u m a s)
  then show ?case  proof -
    let ?cs="head@tail"
    from `u \<in> set m \<union> set a` have x:"fv_msg u \<subseteq> fvc (a|m}t)" by(auto)
    from  `unify_msg [(t, u)] = Some s` have "sdom_msg s \<subseteq> fv_eqs_msg [(t, u)]" by(rule l3_msg)
    also have "... \<subseteq> fv_msg t \<union> fv_msg u" by(auto simp add:fv_eqs_msg_def fv_msg_def)
    also have "... \<subseteq> fv_msg t \<union> fvc (a|m}t)" using x by(auto simp add:Un_commute Un_assoc insert_commute)
    finally have sdominc:"sdom_msg s \<subseteq> fvc (a|m}t)" by(auto)

    from `s \<noteq> Variable` obtain x where xdef:"x \<in> sdom_msg s" by(auto simp add:sdom_msg_def_real)
    from this and sdominc have "x \<in> fvc (a|m}t)" by auto
    then have part1:"x \<in> fvs(head @ (a|m}t)#tail)" by auto

    from  `unify_msg [(t, u)] = Some s` have "sdom_msg s \<inter> svran_msg s = {}" by(rule l3_msg)
    from this and xdef have svninc:"x \<notin> svran_msg s" by auto

    have "fvs (sapplys s ?cs) \<subseteq> fvs ?cs - sdom_msg s \<union> svran_msg s" (is "?lhs \<subseteq> ?rhs") by(rule fv_sapplys_sdom_svran)
    moreover from xdef and svninc have "x \<notin> ?rhs" by auto
    ultimately have "x \<notin> ?lhs" by blast
    then have "x \<notin> fvs ([] @ sapplys s (head @ tail))" by auto
    
    from this and part1 show ?case by blast
  qed
next
  case (rer1_ksub u agent a s m t)
  then show ?case
  proof -
    have "agent \<in> fv_msg (Pub_encrypt u (Variable agent))" by(simp add:fv_msg_simps)
    from this and `Pub_encrypt u (Variable agent) \<in> set a`
    have part1:"agent \<in> fvs (head @ a|m} t  # tail)" by auto

    let ?cs="head @ a|m} t  # tail"
    let ?s="Variable(agent := Const ''intruder'')"
    have "svran_msg ?s = {}" and "sdom_msg ?s={agent}"
      by(auto simp add:svran_msg_def_real sran_msg_def_real sdom_msg_def_real fv_msg_def)
    then have svran:"svran_msg s = {}" "sdom_msg s = {agent}"
      by(simp_all add:`s = ?s`)
    have "fvs (sapplys s ?cs) \<subseteq> fvs ?cs - sdom_msg s \<union> svran_msg s" (is "?lhs \<subseteq> ?rhs") by(rule fv_sapplys_sdom_svran)
    then have "fvs (sapplys s ?cs) \<subseteq> fvs ?cs - {agent}" by(simp add:svran)

    moreover have "fvs ([sapplyc s (a|m} t )] @ sapplys s (head @ tail)) = (fvs (sapplys s ?cs))" (is "?lhs = ?rhs")
      by(simp add:sapplys_def)
    ultimately have "?lhs \<subseteq> fvs ?cs - {agent}" by simp
    then have "agent \<notin> ?lhs" by blast
    from this and  part1 show ?thesis by blast
  qed
qed(auto)

lemma rer1_weight: "c \<leadsto>1[s] cs \<Longrightarrow> s = Variable \<Longrightarrow> weights cs < weight c"
proof(induction c s cs rule:rer1.induct)
  case (rer1_sdec x u k head tail m t)
  then show ?case
  proof -
    from non_zero_theta have "Suc 0 \<le> \<theta> t" by (simp add: Suc_leI)
      then  have "\<chi> u * \<theta> t < (1+\<chi> u)*(\<theta> t)" and "\<theta> k \<le> \<theta> k* \<theta> t" by auto
    then have "\<chi> u * \<theta> t + \<theta> k < (1 + \<chi> u + \<theta> k) * \<theta> t" (is "?lhs < ?rhs")
      by (metis add_less_cancel_right add_less_mono distrib_right le_neq_implies_less)
    then have "\<chi>l head * \<chi>l tail * ?lhs < \<chi>l head * \<chi>l tail * ?rhs" by auto
    then have "\<chi> u * (\<chi>l head * \<chi>l tail) * \<theta> t + \<chi>l head * \<chi>l tail * \<theta> k
    < \<chi>l head * (\<chi>l tail + (\<chi> u + \<theta> k) * \<chi>l tail) * \<theta> t" 
    (* sledgehammer *)
    proof -
      have f1: "\<chi> u * (\<chi>l head * \<chi>l tail) * \<theta> t + \<chi>l head * \<chi>l tail * \<theta> k = \<theta> t * \<chi> u * (\<chi>l tail * \<chi>l head) + \<theta> k * (\<chi>l tail * \<chi>l head)"
        by simp
      have f2: "\<chi>l head * (\<chi>l tail + (\<chi> u + \<theta> k) * \<chi>l tail) = (\<chi> u + \<theta> k + 1) * (\<chi>l head * \<chi>l tail)"
        by (metis (no_types) semiring_normalization_rules(19) semiring_normalization_rules(3))
      have "1 + \<chi> u + \<theta> k = \<chi> u + \<theta> k + 1"
        by auto
      then have "\<chi>l head * (\<chi>l tail + (\<chi> u + \<theta> k) * \<chi>l tail) * \<theta> t = (1 + \<chi> u + \<theta> k) * (\<theta> t * (\<chi>l tail * \<chi>l head))"
        using f2 by (metis semiring_normalization_rules(19) semiring_normalization_rules(7))
      then have "\<chi>l head * (\<chi>l tail + (\<chi> u + \<theta> k) * \<chi>l tail) * \<theta> t = (1 + \<chi> u + \<theta> k) * (\<chi>l head * \<chi>l tail * \<theta> t)"
        by simp
      then have "\<chi>l head * (\<chi>l tail + (\<chi> u + \<theta> k) * \<chi>l tail) * \<theta> t = \<chi>l head * \<chi>l tail * ((1 + \<chi> u + \<theta> k) * \<theta> t)"
        by (simp add: semiring_normalization_rules(19))
      then show ?thesis
        using f1 by (metis (no_types) \<open>\<chi>l head * \<chi>l tail * (\<chi> u * \<theta> t + \<theta> k) < \<chi>l head * \<chi>l tail * ((1 + \<chi> u + \<theta> k) * \<theta> t)\<close> semiring_normalization_rules(1) semiring_normalization_rules(7))
    qed
      (* end sledgehammer *)
    from this and rer1_sdec show ?case by auto
  qed
next
  case (rer1_ksub u agent a s m t)
  from ` s = Variable(agent := Const ''intruder'')` have "s agent = Const ''intruder''" by simp
  moreover from `s=Variable` have "s agent = Variable agent" by simp
  ultimately have False by simp
  then show ?case by(rule FalseE)
qed (simp_all add: add_mult_distrib2)
end