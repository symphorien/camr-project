chapter {* camr project *}

theory Protocol imports Main Unification begin

(* definition of messages *)
type_synonym var = string
type_synonym const = string
datatype msg =
Hash msg | Concat msg msg | Sym_encrypt msg msg | Pub_encrypt msg msg | Sign msg msg
| Const const | Variable var
(* Pub_encrypt content key  and so on*)

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
  sorry

lemma msg_of_term_embed [simp]: "msg_of_term (embed x) = x"
proof(induction x)
qed auto

lemma embed_msg_of_term [simp]: "wf_term arity x \<Longrightarrow> embed (msg_of_term x) = x"
  sorry

end
