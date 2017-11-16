chapter {* camr project *}

theory Term imports Main Unification begin
(* assignment 5 *)
(* (a) *)

(* definition of messages *)
type_synonym var = string
type_synonym const = string
datatype msg =
Hash msg | Concat msg msg | Sym_encrypt msg msg | Pub_encrypt msg msg | Sign msg msg
| Const const | Variable var
(* Pub_encrypt content key  and so on*)

(* (b) *)
(* embedding *)
datatype symbol =
SHash | SConcat | SSym_encrypt | SPub_encrypt | SSign | SConst const
fun arity :: "symbol \<Rightarrow> nat" where
"arity SHash = 1"
| "arity SConcat = 2"
| "arity SSym_encrypt = 2"
| "arity SPub_encrypt = 2"
| "arity SSign = 2"
| "arity (SConst _) = 0"

(* (c) *)
type_synonym msg_term = "(symbol, var) term"

fun embed :: "msg \<Rightarrow> msg_term" where
"embed (Hash x) = Fun SHash [embed x]"
| "embed (Concat x y) = Fun SConcat [embed x, embed y]"
| "embed (Sym_encrypt x y) = Fun SSym_encrypt [embed x, embed y]"
| "embed (Pub_encrypt x y) = Fun SPub_encrypt [embed x, embed y]"
| "embed (Sign x y) = Fun SSign [embed x, embed y]"
| "embed (Const x) = Fun (SConst x) []"
| "embed (Variable x) = Var x"

fun msg_of_term :: "msg_term \<Rightarrow> msg" where
"msg_of_term (Fun SHash [x]) = Hash (msg_of_term x)"
| "msg_of_term (Fun SConcat [x, y]) = Concat (msg_of_term x) (msg_of_term y)"
| "msg_of_term (Fun SSym_encrypt [x, y]) = Sym_encrypt (msg_of_term x) (msg_of_term y)"
| "msg_of_term (Fun SPub_encrypt [x, y]) = Pub_encrypt (msg_of_term x) (msg_of_term y)"
| "msg_of_term (Fun SSign [x, y]) = Sign (msg_of_term x) (msg_of_term y)"
| "msg_of_term (Fun (SConst x) []) = Const x"
| "msg_of_term (Var x) = Variable x"

(* embedding lemmas *)
lemma wf_term_embed [simp]: "wf_term arity (embed msg)"
proof(induction msg)
qed(auto intro:wf_term.intros)

lemma msg_of_term_embed [simp]: "msg_of_term (embed x) = x"
proof(induction x)
qed auto

lemma embed_msg_of_term [simp]: "wf_term arity x \<Longrightarrow> embed (msg_of_term x) = x"
proof(induction rule:wf_term.induct)
case (wf_term_intro_var uu)
then show ?case by auto
next
case (wf_term_intro_fun l f)
  then show ?case
(* arity goes up to 2 so pattern match on up to 2 elements of l*)
  proof(cases f;cases l;(cases "tl l")?)
  qed(auto simp add:"wf_term_intro_fun.IH")
qed

(* (c) : transfer of various functions via embedding 
   naming convention: ${fn} \<rightarrow> ${fn}_msg_*)
(* fv *)
definition fv_msg:: "msg \<Rightarrow> var set" where
"fv_msg m = fv (embed m)"

(* substs *)
type_synonym subst_msg = "var \<Rightarrow> msg"
fun embed_subst :: "subst_msg \<Rightarrow> (var \<Rightarrow> msg_term)" where
"embed_subst s = embed o s"
fun subst_from_embed :: "(var \<Rightarrow> msg_term) \<Rightarrow> subst_msg"  where
"subst_from_embed s = msg_of_term o s"

lemma embed_subst_from_embed [simp]: "wf_subst arity x \<Longrightarrow> embed \<circ> (msg_of_term \<circ> x) = x"
proof(induction rule:wf_subst.induct)
  case (1 \<sigma>)
  then show ?case by(auto simp add:fun_eq_iff)
qed

(* sapply *)
definition sapply_msg :: "subst_msg \<Rightarrow> msg \<Rightarrow> msg" where
"sapply_msg s m = msg_of_term (sapply (embed_subst s) (embed m))"

(* unifies *)
type_synonym eq_msg = "msg \<times> msg"
fun embed_eq :: "eq_msg \<Rightarrow> (symbol, var) equation" where
"embed_eq (a, b) = (embed a, embed b)"

definition unifies_msg :: "subst_msg \<Rightarrow> eq_msg \<Rightarrow> bool" where
  "unifies_msg s eq = unifies (embed_subst s) (embed_eq eq)"

(* unifiess *)
definition unifiess_msg :: "subst_msg \<Rightarrow> eq_msg list \<Rightarrow> bool" where
  "unifiess_msg s eqs = unifiess (embed_subst s) (map embed_eq eqs)"

(* unify *)
fun bind:: "('a\<Rightarrow>'b) \<Rightarrow> 'a option \<Rightarrow> 'b option" where
"bind f x = (case x of None \<Rightarrow> None | (Some x) \<Rightarrow> Some (f x))"

definition unify_msg :: "eq_msg list \<Rightarrow> subst_msg option" where
"unify_msg eqs = bind subst_from_embed (unify (map embed_eq eqs))"


(* (e) *)
lemma unify_msg_return: "unify_msg l = Some \<sigma> \<Longrightarrow> unifiess_msg \<sigma> l"
proof -
  let ?s="map embed_eq l"
  assume returns:"unify_msg l = Some \<sigma>"
(* first we need to show that x is well formed *)
  then obtain x where xdef:"unify ?s = Some x" and sigmadef:"\<sigma> = msg_of_term \<circ> x"
    by(auto simp add:unify_msg_def unifiess_msg_def split:option.split_asm)
  have "wf_eqs arity ?s" 
    by(auto intro!:wf_eqs.intros wf_eq.intros)
  from xdef and this have "wf_subst arity x" by(rule wf_subst_unify)
(* now we can use the embedding easily *)
  show ?thesis
    apply(auto simp add:unify_msg_def xdef sigmadef unifiess_msg_def)
    apply(rule unify_return)
  apply(simp only:xdef `wf_subst arity x` embed_subst_from_embed)
    done
qed

end
