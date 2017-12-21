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

fun rer_succ_aux:: "system \<Rightarrow> system \<Rightarrow> (subst_msg \<times> system) list" where
  "rer_succ_aux head [] = []" |
  "rer_succ_aux head (c#tail) = 
rer_succ_aux (head@[c]) tail @ (map
  (%(s, cs). 
     (s,
      cs@(sapplys s (head@tail))
     )
  )
  (rer1_succ c)
)"

lemma rer_succ_aux_sound: "(s, cs') \<in> set (rer_succ_aux head tail) \<Longrightarrow> (head@tail) \<leadsto>[s] cs'"
proof(induction head tail arbitrary:s cs' rule:rer_succ_aux.induct)
  case (1 head)
  then show ?case by simp
next
  case (2 head c tail)
  then show ?case
  proof(cases "(s, cs') \<in> set (rer_succ_aux (head@[c]) tail)")
    case True
    then have "((head @ [c]) @ tail)\<leadsto>[s] cs'" by(rule 2)
    then show ?thesis by(simp)
next
  case False
  from this and "2"(2) have "(s, cs') \<in> set (map
  (%(s, cs). 
     (s,
      cs@(sapplys s (head@tail))
     )
  )
  (rer1_succ c)
)" by simp
  then obtain cs where csdef:"cs' = cs@(sapplys s (head@tail))" and in_rer1_succ:"(s, cs) \<in> set (rer1_succ c)" by auto
  moreover from in_rer1_succ have "c \<leadsto>1[s] cs" by(rule rer1_succ_sound)
  ultimately show ?thesis by(auto intro!:rer.intros)
qed
qed

(* ok, this is exactly the same proof that for through_m_ribosom; I could have done a proper
general theorem *)
lemma rer_succ_aux_ribosom: "set (rer_succ_aux head tail) \<subseteq> set (rer_succ_aux [] (head@tail))"
proof(induction "rev head" arbitrary:head tail)
case Nil
  then show ?case by simp
next
  case (Cons u rhead head)
  then have "head = rev (u#rhead)" by simp
  then have headdef:"head = (rev rhead) @ [u]" by simp
  have "rhead = rev (rev rhead)" by simp
  then have "set (rer_succ_aux (rev rhead) (u # tail))
\<subseteq> set (rer_succ_aux [] (rev rhead @ u # tail))" by(rule Cons(1))
  moreover have "rev rhead @ u # tail = head @ tail" by(simp add: headdef)
  ultimately have "set (rer_succ_aux (rev rhead) (u # tail)) \<subseteq> set (rer_succ_aux [] (head @ tail))" by simp
  moreover have "set (rer_succ_aux ((rev rhead) @ [u]) tail) \<subseteq> set (rer_succ_aux (rev rhead) (u # tail))" by auto
  then have "set (rer_succ_aux head tail) \<subseteq> set (rer_succ_aux (rev rhead) (u # tail))" by(simp add:headdef)
  ultimately show ?case by blast
qed

fun rer_succ:: "system \<Rightarrow> (subst_msg \<times> system) list" where
"rer_succ cs = rer_succ_aux [] cs"

lemma rer_succ_complete: "cs \<leadsto>[s] cs' \<Longrightarrow> (s, cs') \<in> set (rer_succ cs)"
proof(induction cs s cs' rule:rer.induct)
  case (1 c s cs head tail)
  then have "(s, cs)\<in> set (rer1_succ c)" by(rule rer1_succ_complete)
  then have "(s, cs @ sapplys s (head @ tail))\<in> set (rer_succ_aux head (c#tail))" (is "?elt \<in> ?set") by auto
  moreover have "?set \<subseteq> set (rer_succ_aux [] (head@c#tail))" by(rule rer_succ_aux_ribosom)
  then have "?set \<subseteq> set (rer_succ (head@c#tail))" by simp
  ultimately show ?case by blast
qed

lemma rer_succ_sound: "(s, cs') \<in> set (rer_succ cs) \<Longrightarrow> cs \<leadsto>[s] cs'"
proof -
  assume "(s, cs') \<in> set (rer_succ cs)"
  then have "(s, cs') \<in> set (rer_succ_aux [] cs)" by simp
  then have "([]@cs) \<leadsto>[s] cs'" by(rule rer_succ_aux_sound)
  then show "cs \<leadsto>[s] cs'" by simp
qed

fun next_step:: "(subst_msg \<times> system) list \<Rightarrow> (subst_msg \<times> system) list" where
"next_step l = (concat (map 
(%(s, cs).
  map (%(s', cs'). (scomp_msg s' s, cs')) (rer_succ cs)
) l
))"


lemma set_next_step: "set (next_step l) = (\<Union> (s, cs) \<in> set l. {(scomp_msg s' s, cs') |cs' s'. cs\<leadsto>[s'] cs'})" (is "_ = ?UN")
proof(rule equalityI; rule subsetI)
  fix x
  assume xin:"x\<in> set(next_step l)"
  then obtain s cs s' cs' where xdef:"x= (scomp_msg s' s, cs')" and rel:"(s', cs')\<in>set (rer_succ cs)" and csdef:"(s, cs)\<in>set l"  by auto
  moreover from rel have "cs \<leadsto>[s'] cs'" by(rule rer_succ_sound)
  ultimately show "x\<in> ?UN" by auto
next
  fix x
  assume xin:"x\<in>?UN"
  then obtain s cs s' cs' where
    xdef:"x= (scomp_msg s' s, cs')" and rel:"cs\<leadsto>[s'] cs'" and csdef:"(s, cs)\<in>set l" 
    by auto
  moreover from rel have "(s', cs')\<in>set (rer_succ cs)" by(rule rer_succ_complete)
  ultimately have "x\<in> set (map (%(s', cs'). (scomp_msg s' s, cs')) (rer_succ cs))" (is "x\<in> set ?L") by auto
  moreover from csdef have "?L \<in> set (map 
(%(s, cs).
  map (%(s', cs'). (scomp_msg s' s, cs')) (rer_succ cs)
) l)" by auto
  ultimately show "x\<in> set (next_step l)" by(auto simp only:set_concat next_step.simps)
qed

lemma wf_empty: "wf {}" by(auto simp add: wf_eq_minimal)

definition steps_set:: "(((subst_msg \<times> system) list) \<times> ((subst_msg \<times> system) list)) set"
  where "steps_set = {((next_step l), l)|l. l\<noteq>[]}"

lemma wf_steps_set:"wf steps_set"
proof -
  let ?orig = "{(y, x). reducesto x y}"
  let ?pairs = "?orig <*lex*> ({}::subst_msg rel)"
  let ?revpairs = "inv_image ?pairs (%(x, y). (y, x))"
  let ?sets = "max_ext ?revpairs"
  have "steps_set \<subseteq> inv_image ?sets set" (is "_ \<subseteq> ?lists")
  proof(rule subsetI)
    fix x
    assume assms:"x \<in> steps_set"
    then obtain l where xdef:"x = (next_step l, l)" and lnonempty:"l\<noteq>[]" by(auto simp del:next_step.simps simp add:steps_set_def)
    have "(set (next_step l), set l) \<in> ?sets"
    proof(rule max_extI)
      fix y
      assume "y \<in> set (next_step l)"
      then obtain s cs s' cs'
        where ydef:"y = (scomp_msg s' s, cs')"
          and cs'def:"(s', cs')\<in> set (rer_succ cs)"
          and csdef: "(s, cs) \<in> set l"
        by auto
      show "\<exists>z\<in>set l. (y, z) \<in> ?revpairs"
      proof(rule bexI[of _ "(s, cs)"])
        from cs'def have "cs \<leadsto>[s'] cs'" by(rule rer_succ_sound)
        then have "reducesto cs cs'" by(auto intro:reducesto.intros)
        then have "(cs', cs) \<in> ?orig" by simp
        then have "((cs', s'), (cs, s)) \<in> ?pairs" by(auto)
        then show "(y, (s, cs)) \<in> ?revpairs" by(auto simp add:inv_image_def ydef)
      qed(simp add:csdef)
    qed(auto simp add:lnonempty)
    from this assms xdef show "x\<in> ?lists" by(auto simp del:next_step.simps simp add:steps_set_def)
  qed
  moreover from termination_red and wf_empty have "wf ?pairs" by(rule wf_lex_prod)
  then have "wf ?revpairs" by auto
  then have "wf ?sets" by(auto intro:max_ext_wf)
  then have "wf ?lists" by auto
  ultimately show ?thesis by(auto intro:wf_subset)
qed

function search_aux :: "(subst_msg \<times> system) list \<Rightarrow> (subst_msg \<times> system) option" where
"search_aux l = (if l=[] then None else (case find (%(s, cs). simples cs) l of Some x \<Rightarrow> Some x | None \<Rightarrow> search_aux (next_step l)))"
  by pat_completeness auto
termination
  apply(relation "steps_set")
  using wf_steps_set apply(auto simp add:steps_set_def simp del:next_step.simps)
  done


lemma "search_aux l = None \<Longrightarrow> (s, cs)\<in> set l \<Longrightarrow> cs \<leadsto>*[s'] cs' \<Longrightarrow> simples cs' \<Longrightarrow> False"
proof(induction l arbitrary:s cs s' rule:search_aux.induct)
  case (1 l)
  then show ?case
  proof(cases "l=[]")
    case True
    from this and "1" show ?thesis by(simp)
  next
    case False
    from `l\<noteq>[]` and `search_aux l = None` have a:"find (\<lambda>a. case a of (s, a) \<Rightarrow> simples a) l = None"
      by(cases)(auto simp del:next_step.simps split:if_split_asm option.split)
    from `l\<noteq>[]` and `search_aux l = None` and this have b:"search_aux (next_step l) = None"
      by(auto simp del:next_step.simps split:if_split_asm option.split)
    from a b "1" False have "\<And>s s' cs. (s, cs) \<in> set (next_step l) \<Longrightarrow>  cs\<leadsto>*[s'] cs' \<Longrightarrow> False" 
      by blast
    from `cs\<leadsto>*[s'] cs'` and `simples cs'` and `(s, cs) \<in> set l` and `search_aux l = None` and this show ?thesis
    proof(induction cs s' cs' arbitrary:s l rule:rer_star.induct)
      case (rer_star_id cs)
      from `(s, cs) \<in> set l` have "l \<noteq> []" by auto
      from `simples cs` and `l\<noteq>[]` and `(s, cs)\<in> set l`
      have "find (\<lambda>(s, y). simples y) l \<noteq> None"
        by(auto simp add:find_None_iff)
      from this and `search_aux l = None` show False
        by(auto simp del:next_step.simps split:if_split_asm option.split_asm)
    next
      case (rer_star_step cs t' cs'' t cs')
      from `cs\<leadsto>[t'] cs''` and `(s, cs)\<in>set l` have c:"(scomp_msg t' s, cs'')\<in> set (next_step l)" (is "(?s, _)\<in>_")
        by (auto simp add:set_next_step simp del:next_step.simps)
      have d:"search_aux (next_step l) = None"
      proof(rule ccontr)
        assume "search_aux (next_step l) \<noteq> None"
        then obtain x where "search_aux (next_step l) =Some x" by auto
        moreover from `(s, cs) \<in> set l` have "l\<noteq>[]" by auto
        ultimately have "search_aux (l) \<noteq> None"
          by(auto simp del:next_step.simps split:if_split_asm option.split)
        from this and `search_aux l = None` show False by blast
      qed
      have "\<And>S CS S'. (S, CS) \<in> set (next_step (next_step l)) \<Longrightarrow> CS\<leadsto>*[S'] cs'  \<Longrightarrow> False"
      proof -
        fix S CS S'
        assume "(S, CS) \<in> set (next_step (next_step l))" "CS\<leadsto>*[S'] cs'"
        from `(?s, cs'')\<in>set (next_step l)` and this and set_next_step[of "next_step l"]
        obtain k T U where "k \<leadsto>[T] CS" and "(U, k)\<in> set (next_step l)"
          by(auto simp del:next_step.simps)
        from this and `CS\<leadsto>*[S'] cs'` have "k \<leadsto>*[scomp_msg S' T] cs'" by(auto intro:rer_star.intros)
        from `(U, k)\<in>set (next_step l)` and this show False by(rule rer_star_step)
      qed
      from `simples cs'` and c and d and this and rer_star_step show False by blast
    qed
  qed
qed
 
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