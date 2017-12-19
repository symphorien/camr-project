chapter {* camr project *}

theory Execute imports Main Unification Term Deduction begin


fun through_m :: "msg list \<Rightarrow> msg list \<Rightarrow> msg list \<Rightarrow> msg \<Rightarrow> (subst_msg \<times> system) list" where
"through_m head [] a t = []" |
"through_m head (u#tail) a t = (
  case u of
    Concat u1 u2 \<Rightarrow>
      [(Variable, [(((u1#u2#head@tail) | (u#a) } t))])]
    | Sym_encrypt m k \<Rightarrow>
      [(Variable, [(((m#head@tail) | (u#a) } t)), (((head@tail) | (u#a) } k))])]
    | Pub_encrypt m (Variable agent) \<Rightarrow> 
        let s = Variable(agent:=(Const ''intruder'')) in
        [(s, [sapplyc s ((head@u#tail)|a}t)])]
    | Pub_encrypt m (Const x) \<Rightarrow> (  
      if x = ''intruder'' then  
        [(Variable, [(((m#head@tail) | (u#a) } t))])]
      else
        []
      )
    | _ \<Rightarrow> []
) @ through_m (head@[u]) tail a t"

lemma through_m_ribosom: "set (through_m head tail a t) \<subseteq> set (through_m [] (head@tail) a t)"
proof(induction "rev head" arbitrary:head tail)
case Nil
  then show ?case by simp
next
  case (Cons u rhead head)
  then have "head = rev (u#rhead)" by simp
  then have headdef:"head = (rev rhead) @ [u]" by simp
  have "rhead = rev (rev rhead)" by simp
  then have "set (through_m (rev rhead) (u # tail) a t)
\<subseteq> set (through_m [] (rev rhead @ u # tail) a t)" by(rule Cons(1))
  moreover have "rev rhead @ u # tail = head @ tail" by(simp add: headdef)
  ultimately have "set (through_m (rev rhead) (u # tail) a t) \<subseteq> set (through_m [] (head @ tail) a t)" by simp
  moreover have "set (through_m ((rev rhead) @ [u]) tail a t) \<subseteq> set (through_m (rev rhead) (u # tail) a t)" by auto
  then have "set (through_m head tail a t) \<subseteq> set (through_m (rev rhead) (u # tail) a t)" by(simp add:headdef)
  ultimately show ?case by blast
qed

lemma through_m_sound: 
  assumes "(s', cs') \<in> set (through_m head tail a t)"
  shows "((head@tail) | a } t) \<leadsto>1[s'] cs'"
  using assms
proof(induction head tail a t rule: through_m.induct)
  case (1 head a t)
  then show ?case by auto
next
  case (2 head u tail a t)
  let ?snd = "through_m (head @ [u]) tail a t"
  let ?fst = "through_m head (u # tail) a t"
  let ?prefix = "case u of
    Concat u1 u2 \<Rightarrow>
      [(Variable, [(((u1#u2#head@tail) | (u#a) } t))])]
    | Sym_encrypt m k \<Rightarrow>
      [(Variable, [(((m#head@tail) | (u#a) } t)), (((head@tail) | (u#a) } k))])]
    | Pub_encrypt m (Variable agent) \<Rightarrow> 
        let s = Variable(agent:=(Const ''intruder'')) in
        [(s, [sapplyc s ((head@u#tail)|a}t)])]
    | Pub_encrypt m (Const x) \<Rightarrow> (  
      if x = ''intruder'' then  
        [(Variable, [(((m#head@tail) | (u#a) } t))])]
      else
        []
      )
    | _ \<Rightarrow> []"
  have decomp:"set ?fst = set ?prefix \<union> set ?snd" by auto
  then show ?case 
  proof (cases "(s', cs') \<in> set ?snd")
    case True
    then show ?thesis using 2 by auto
  next
    case False
    then have "(s', cs') \<in> set ?prefix" using assms decomp 2 by blast
    then show ?thesis by(cases u)(auto intro!: rer1.intros split: msg.split_asm simp add: Let_def simp del: fun_upd_apply)
  qed
qed

fun through_all :: "msg list \<Rightarrow> msg \<Rightarrow> (subst_msg \<times> system) list" where
  "through_all _ (Variable _) = []" |
  "through_all l t  = 
    concat (map (%u. (case unify_msg [(t, u)] of
      None \<Rightarrow> []
    | Some s \<Rightarrow> [(s, [])]
    )) l)"

lemma through_all_sound:
  assumes "(s, cs) \<in> set (through_all (m@a) t)"
          "c = m|a}t"
        shows "c \<leadsto>1[s] cs"
  using assms
proof(cases t)
qed(auto intro:rer1.intros)


fun through_t :: "constraint \<Rightarrow> (subst_msg \<times> system) option" where
  "through_t (m|a}Concat x y) = Some (Variable, [(m|a}x), (m|a}y)])"
| "through_t (m|a}Sym_encrypt x y) =  Some (Variable, [(m|a}x), (m|a}y)])"
| "through_t (m|a}Pub_encrypt x y) = Some (Variable, [(m|a}x), (m|a}y)])"
| "through_t (m|a}Sign x y) = (if y = Const ''intruder'' then  Some (Variable, [(m|a}x)]) else None)"
| "through_t (m|a}Hash x) = Some (Variable, [(m|a}x)])"
| "through_t _ = None"

lemma through_t_sound:"Some (s, cs) = (through_t c) \<Longrightarrow> c \<leadsto>1[s] cs"
proof(cases c)
  case (Constraint a m t)
  show "Some (s, cs) = (through_t c) \<Longrightarrow> c \<leadsto>1[s] cs" 
    apply(cases t)
          apply(auto simp add:Constraint intro!:rer1.intros split:if_split_asm)
    done
qed

fun rer1_succ:: "constraint \<Rightarrow> (subst_msg \<times> system) list" where
  "rer1_succ (m|a}t) = 
(through_all (m@a) t) @ (
(through_m [] m a t) @ ( 
(case through_t (m|a}t) of None \<Rightarrow> [] | Some x \<Rightarrow> [x])))"

lemma rer1_succ_sound: "(s, cs) \<in> set (rer1_succ c) \<Longrightarrow> c \<leadsto>1[s] cs"
proof (cases c)
  case (Constraint m a t)
  assume in_set: "(s, cs) \<in> set (rer1_succ c)" 
  have in_union: "(set (rer1_succ (m|a}t))) = (set (through_all (m@a) t)) \<union> (set (through_m [] m a t)) \<union> (set (case through_t (m|a}t) of None \<Rightarrow> [] | Some x \<Rightarrow> [x]))" 
    (is "_ = ?Setall \<union> ?Setm \<union> ?Sett") by auto
  then show ?thesis 
  proof (cases "(s, cs) \<in> ?Setall")
    case True
    then show ?thesis using Constraint by (rule through_all_sound)
  next
    case ex: False
    then show ?thesis
    proof(cases "(s, cs) \<in> ?Setm")
      case True
      thm through_m_sound through_m_sound[of s cs "[]" m a t]
      then have "([] @ m)|a} t \<leadsto>1[s] cs" by (rule through_m_sound)
      then show ?thesis using Constraint by simp
    next
      case False
      then have "(s, cs) \<in> ?Sett" using ex in_union in_set Constraint by simp
      then show ?thesis using Constraint by (auto simp add: through_t_sound)
    qed
  qed
qed

lemma rer1_succ_complete: "c \<leadsto>1[s] cs \<Longrightarrow> (s, cs) \<in> set (rer1_succ c)"
proof(induction c s cs rule:rer1.induct)
  case (rer1_unify t u a m s)
  then have "(s, []) \<in> set (through_all (m@a) t)"
    apply(cases t; cases "u\<in>set a")
                 apply(auto simp add:sym[of "Some s" _] intro:bexI[of _ "u" "set a"])
         apply(auto simp add:sym[of "Some s" _] intro:bexI[of _ "u" "set m"])
    done    
  then show ?case by simp
next
  case (rer1_proj x u v head tail a t)
  then have "(Variable, [(u # v # head @ tail)|(x # a)} t ]) \<in> set (through_m head (x # tail) a t)" (is "?x \<in> ?s")
    by(auto)
  moreover have "?s \<subseteq> set (through_m [] (head@x#tail) a t)" by(rule through_m_ribosom)
  ultimately have "?x \<in> set (through_m [] (head @ x # tail) a t)"
    by blast
  then show ?case by simp
next
  case (rer1_sdec x u k head tail a t)
  then have "(Variable,
     [(u # head @ tail)|(x # a)} t , (head @ tail)|(x # a)} k ]) \<in> set (through_m head (x # tail) a t)" (is "?x \<in> ?s")
    by(auto)
  moreover have "?s \<subseteq> set (through_m [] (head@x#tail) a t)" by(rule through_m_ribosom)
  ultimately have "?x \<in> set (through_m [] (head @ x # tail) a t)"
    by blast
  then show ?case by simp
next
  case (rer1_adec x u head tail a t)
   then have "(Variable, [(u # head @ tail)|(x # a)} t ]) \<in> set (through_m head (x # tail) a t)" (is "?x \<in> ?s")
    by(auto)
  moreover have "?s \<subseteq> set (through_m [] (head@x#tail) a t)" by(rule through_m_ribosom)
  ultimately have "?x \<in> set (through_m [] (head @ x # tail) a t)"
    by blast
  then show ?case by simp
next
  case (rer1_ksub u agent m s a t)
  let ?x="Pub_encrypt u (Variable agent)"
  from rer1_ksub(1) and split_list[of "?x" "m"]  obtain head tail where mdef:"m = head @ ?x#tail" by blast
 then have " (s, [sapplyc s (m|a} t )]) \<in> set (through_m head (?x # tail) a t)" (is "?elt \<in> ?s")
   by(auto simp add:rer1_ksub Let_def sapplyc_def)
  moreover have "?s \<subseteq> set (through_m [] (head@?x#tail) a t)" by(rule through_m_ribosom)
  ultimately have "?elt \<in> set (through_m [] (head @ ?x # tail) a t)"
    by blast
  then show ?case by (simp add:mdef)
qed auto

fun rer_succ_aux:: "system \<Rightarrow> system \<Rightarrow> (subst_msg \<times> system) list \<Rightarrow> (subst_msg \<times> system) list" where
  "rer_succ_aux head [] acc = acc" |
  "rer_succ_aux head (c#tail) acc = 
rer_succ_aux (head@[c]) tail (fold 
  (%(s, cs) acc2. 
     (s,
      cs@(sapplys s (head@tail))
     )#acc2
  )
  (rer1_succ c)
  acc
)"

fun rer_succ:: "system \<Rightarrow> (subst_msg \<times> system) list" where
"rer_succ cs = rer_succ_aux [] cs []"

fun next_step:: "(subst_msg \<times> system) list \<Rightarrow> (subst_msg \<times> system) list" where
"next_step l = (concat (map 
(%(s, cs).
  map (%(s', cs'). (scomp_msg s' s, cs')) (rer_succ cs)
) l
))"

function search_aux :: "(subst_msg \<times> system) list \<Rightarrow> (subst_msg \<times> system) option" where
"search_aux l = (if l=[] then None else (case find (%(s, cs). simples cs) l of Some x \<Rightarrow> Some x | None \<Rightarrow> search_aux (next_step l)))"
  by pat_completeness auto
termination
  (* by (auto simp add:termination_red) *)
  sorry

fun search:: "system \<Rightarrow> (subst_msg \<times> system) option" where
"search cs = search_aux [(Variable, cs)]"

definition KTP:: "msg \<Rightarrow> msg \<Rightarrow> msg \<Rightarrow> msg \<Rightarrow> system"
  where
"KTP A0 B0 A1 B1 =
(let
  IK0 = [Const ''A'', Const ''B'', Const ''intruder''];
  IK1 = (Pub_encrypt (Sign (Const ''k0'') A0) B0) # IK0;
  IK2 = (Sym_encrypt (Const ''m1'') (Variable ''K1''))#IK1
in [
  (IK0|[]}A0), 
  (IK0|[]}A1),
  (IK1|[]} (Pub_encrypt (Sign (Variable ''K1'') A1) B1)),
  (IK2|[]} (Sym_encrypt (Variable ''Z0'') (Variable ''K1''))),
  (IK2|[]} (Concat (Variable ''K1'') (Variable ''Z0'')))
  ]
)"

definition "A0 = Variable ''A0''"
definition "A1 = Const ''A''"
definition "B0 = Variable ''B0''"
definition "B1 = Const ''B''"

value "find (%(s, cs). simples cs) (rer_succ (KTP A0 B0 A1 B1))"
value "rer_succ (KTP A0 B0 A1 B1)"
value "(next_step ([(Variable, (KTP A0 B0 A1 B1))]))"

value "map_option (%(s, cs). (cs, map (%v. (v, s v)) [''A0'', ''B0'', ''K1'', ''Z0''])) (search (KTP A0 B0 A1 B1))"

end 