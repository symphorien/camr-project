chapter {* camr project *}

theory Protocol imports Main Unification begin

(* definition of messages *)
type_synonym var = string
type_synonym const = string
datatype msg =
Hash msg | Concat msg msg | Sym_encrypt msg msg | Pub_encrypt msg msg | Sign msg msg
| Const const | Var var
(* Pub_encrypt content key  and so on*)

datatype symbol =
SHash | SConcat | SSym_encrypt | SPub_encrypt | SSign | SConst | SVar
fun arity :: "symbol \<Rightarrow> nat" where
"arity SHash = 1"
| "arity SConcat = 2"
| "arity SSym_encrypt = 2"
| "arity SPub_encrypt = 2"
| "arity SSign = 2"
| "arity SConst = 0"
| "arity SVar = 0"


end
