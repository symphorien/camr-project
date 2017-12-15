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
    | Pub_encrypt m x \<Rightarrow> (
      if x = Const ''intruder'' then 
        (Variable, [(((m#head@tail) | (u#a) } t))])#acc
      else
        acc
      )
    | _ \<Rightarrow> acc
)
"
lemma assumes acc:"\<forall> (s, cs)  \<in> set acc. c \<leadsto>1[s] cs" "(s', cs') \<in> set (through_m head tail a t acc)"
  shows " c \<leadsto>1[s'] cs'"
  thm through_m.induct
  using assms
proof(induction head a t acc arbitrary: c s' cs' rule:through_m.induct)
  case (1 head a t acc)
  then show ?case

next
  case (2 head u tail a t acc)
  then show ?case sorry
qed
  case Nil
  then show ?case sorry
next
  case (Cons a tail)
  then show ?case sorry
qed
  case Nil
  from this acc show ?case by(auto)
next
  case (Cons u tail)
  from this and assms show ?thesis
  proof(cases u)
    case (Hash x1)
    from assms and Cons and this show ?thesis
      apply(auto intro!:rer1.intros)
  next
    case (Concat x21 x22)
    then show ?thesis sorry
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
fun through_all:: "msg list \<Rightarrow> msg \<Rightarrow> (subst_msg \<times> system) list \<Rightarrow> (subst_msg \<times> system) list" where
"through_all [] t acc = acc" |
"through_all _ (Variable _) acc = acc" |
"through_all (u#terms) t acc =
through_all terms t (case unify_msg [(t, u)] of
None \<Rightarrow> acc
| Some s \<Rightarrow> (Variable, [])#acc
)
"

fun through_t:: "constraint \<Rightarrow> (subst_msg \<times> system) option" where
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
(case through_t (m|a}t) of None \<Rightarrow> [] | Some x \<Rightarrow> [x]))
"

lemma "(s, cs) \<in> set (rer1_succ c) \<Longrightarrow> c \<leadsto>1[s] cs"
proof(cases c)
  case (Constraint a m t)
  then show ?thesis
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
)
"
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
in [(IK0|[]}A0), (IK0|[]}A1),
  (IK1|[]} (Sign (Pub_encrypt (Variable ''K1'') A1) B1)),
  (IK2|[]} (Sym_encrypt (Variable ''Z0'') (Variable ''K1''))),
  (IK2|[]} (Concat (Variable ''K1'') (Variable ''Z0'')))
]
)"

definition "A0 = Variable ''A0''"
definition "A1 = Variable ''A''"
definition "B0 = Variable ''B0''"
definition "B1 = Variable ''B''"

value "find (%(s, cs). simples cs) (rer_succ (KTP A0 B0 A1 B1))"
(* value "map_option (%(s, cs). map (%v. (v, s v)) [''A0'', ''B0'', ''K1'', ''Z0'']) (search (KTP A0 B0 A1 B1))" *)
value "rer_succ (KTP A0 B0 A1 B1)"
value "(next_step ([(Variable, (KTP A0 B0 A1 B1))]))"
value "find (%(s, cs). simples cs) (next_step (next_step (next_step ([(Variable, (KTP A0 B0 A1 B1))]))))"


end 