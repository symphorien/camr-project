chapter {* camr project *}

theory Execute imports Main Unification Term Deduction begin


fun through_m:: "msg list \<Rightarrow> msg list \<Rightarrow> msg list \<Rightarrow> msg \<Rightarrow> (subst_msg \<times> system) list \<Rightarrow> (subst_msg \<times> system) list" where
"through_m head [] a t acc = acc" |
"through_m head (u#tail) a t acc = through_m (head@[u]) tail a t (
  case u of
    Concat u1 u2 \<Rightarrow>
      (Variable, [(((u1#u2#head@tail) | (u#a) } t))])#acc
    | Sym_encrypt m k \<Rightarrow>
      (Variable, [(((m#head@tail) | (u#a) } t)), (((head@tail) | (u#a) } k))])#acc
    | Pub_encrypt m (Variable agent) \<Rightarrow> 
        let s = Variable(agent:=(Const ''intruder'')) in
        (s, [sapplyc s ((head@u#tail)|a}t)])#acc
    | Pub_encrypt m (Const x) \<Rightarrow> (  (* changed from x to (Const x) *)
      if x = ''intruder'' then  
        (Variable, [(((m#head@tail) | (u#a) } t))])#acc
      else
        acc
      )
    | _ \<Rightarrow> acc
)"

fun through_m2:: "msg list \<Rightarrow> msg list \<Rightarrow> msg list \<Rightarrow> msg \<Rightarrow> (subst_msg \<times> system) list \<Rightarrow> (subst_msg \<times> system) list" where
"through_m2 head [] a t acc = acc" |
"through_m2 head ((Concat u1 u2)#tail) a t acc = through_m2 (head@[(Concat u1 u2)]) tail a t (Variable, [(((u1#u2#head@tail) | (u#a) } t))])#acc" |
"through_m2 head ((Sym_encrypt m k)#tail) a t acc = through_m2 (head@[(Sym_encrypt m k)]) tail a t (Variable, [(((m#head@tail) | (u#a) } t)), (((head@tail) | (u#a) } k))])#acc" |
    | Pub_encrypt m (Variable agent) \<Rightarrow> 
        let s = Variable(agent:=(Const ''intruder'')) in
        (s, [sapplyc s ((head@u#tail)|a}t)])#acc
    | Pub_encrypt m (Const x) \<Rightarrow> (  (* changed from x to (Const x) *)
      if x = ''intruder'' then  
        (Variable, [(((m#head@tail) | (u#a) } t))])#acc
      else
        acc
      )
    | _ \<Rightarrow> acc
)"

print_theorems

(*

| rer1_proj: "x=Concat u v \<Longrightarrow> (head@x#tail) | m } t \<leadsto>1[Variable] [ (u#v#head@tail) | (x#m) } t ]"
| rer1_sdec: "x=Sym_encrypt u k \<Longrightarrow> (head@x#tail) | m } t \<leadsto>1[Variable]
 [  ((u#head@tail) | (x#m) } t) ,
    ((head@tail) | (x#m) } k)     ]"
| rer1_adec: "x=Pub_encrypt u (Const ''intruder'') \<Longrightarrow> (head@x#tail) | m } t \<leadsto>1[Variable]
 [ ((u#head@tail) | (x#m) } t) ]"
| rer1_ksub: "Pub_encrypt u (Variable agent) \<in> set a \<Longrightarrow>
s=(Variable (agent:=Const ''intruder'')) \<Longrightarrow>
a|m}t  \<leadsto>1[s] [ sapplyc s (a|m}t) ]"

Concat u1 u2 \<Rightarrow>
            (Variable,
             [(u1 # u2 # head @ tail)|(u # a)} t ]) #
            acc
*)
lemma through_m_sound: 
  assumes "\<forall> (s, cs)  \<in> set acc. c \<leadsto>1[s] cs" 
    "(s', cs') \<in> set (through_m head tail a t acc)"
  shows "c \<leadsto>1[s'] cs'"
  using assms
proof(induction tail)
  case Nil
  from this assms show ?case by(auto)
next
  case (Cons u tail)
  from this and assms show ?thesis
  proof (cases "(s', cs') \<in> set (through_m head tail a t acc)")
    case True
    then show ?thesis using Cons by auto
  next
    case False
    then have "[(s', cs')] = through_m head [u] a t acc" using Cons by auto 
    then show ?thesis 
    proof(cases u)
      case (Hash x1)
      from assms Cons Hash show ?thesis sorry
          (*apply(auto intro!:rer1.intros)*)
    next
      case (Concat u1 u2)
      then have "(s', cs') = (Variable, [(u1 # u2 # head @ tail)|(u # a)} t ])" using Concat False Cons by (auto)
      then show ?thesis using Cons Concat by (auto intro!: rer1.intros split: if_split_asm if_splits)
      using assms Concat Cons by (auto intro!: rer1.intros simp add: through_m.elims)
  next
    case (Sym_encrypt x31 x32)
    then show ?thesis sorry
  next
    case (Pub_encrypt x41 x42)
    then show ?thesis sorry
  next
    case (Sign x51 x52)
    then show ?thesis sorry
  next
    case (Const x6)
    then show ?thesis sorry
  next
    case (Variable x7)
    then show ?thesis sorry
  qed
qed (auto simp add:Cons intro!:rer1.intros split:if_split_asm)
qed

fun through_all :: "msg list \<Rightarrow> msg \<Rightarrow> (subst_msg \<times> system) list \<Rightarrow> (subst_msg \<times> system) list" where
  "through_all [] t acc = acc" |
  "through_all _ (Variable _) acc = acc" |
  "through_all (u#terms) t acc = 
    through_all terms t (case unify_msg [(t, u)] of
      None \<Rightarrow> acc
    | Some s \<Rightarrow> (s, [])#acc (* CHANGED FROM: Some s => (Variable, [])#acc *)
    )"


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
through_all (m@a) t 
(through_m [] m a t
(case through_t (m|a}t) of None \<Rightarrow> [] | Some x \<Rightarrow> [x]))"

lemma rer1_succ_sound: "(s, cs) \<in> set (rer1_succ c) \<Longrightarrow> c \<leadsto>1[s] cs"
proof(cases c)
  case (Constraint a m t)
  then show ?thesis sorry
  proof(cases t)
  qed
qed

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

term "fold"
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