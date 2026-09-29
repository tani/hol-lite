theory HOL_Lite_Syntax
  imports Main
begin

section \<open>Syntax of HOL-Lite\<close>

text \<open>
  HOL-Lite is a minimal HOL Light-style kernel.  This theory fixes types and terms.
  Terms use de Bruijn indices for bound variables and named, typed free variables,
  so alpha-equivalence coincides with equality.
\<close>

subsection \<open>Types\<close>

type_synonym name = string

text \<open>Types are type variables and applications of type constructors.\<close>

datatype ty = TyVar name | TyApp name "ty list"

abbreviation boolT :: ty where
  "boolT \<equiv> TyApp ''bool'' []"

abbreviation funT :: "ty \<Rightarrow> ty \<Rightarrow> ty" where
  "funT a b \<equiv> TyApp ''fun'' [a, b]"

subsection \<open>Terms\<close>

text \<open>
  @{term "Bv i"} is a de Bruijn index; @{term "Abs \<sigma> b"} binds @{term "Bv 0"} in @{term b}.
  Free variables are named and typed; constants carry their instantiated type.
\<close>

datatype tm = Fv name ty | Bv nat | Cst name ty | App tm tm | Abs ty tm

subsection \<open>Type substitution\<close>

text \<open>Substitutions on type variables are total maps (identity outside a finite part).\<close>

fun tsubst :: "(name \<Rightarrow> ty) \<Rightarrow> ty \<Rightarrow> ty" where
  "tsubst \<theta> (TyVar a) = \<theta> a"
| "tsubst \<theta> (TyApp c ts) = TyApp c (map (tsubst \<theta>) ts)"

lemma tsubst_boolT [simp]: "tsubst \<theta> boolT = boolT"
  by simp

lemma tsubst_funT [simp]: "tsubst \<theta> (funT a b) = funT (tsubst \<theta> a) (tsubst \<theta> b)"
  by simp

lemma tsubst_comp: "tsubst \<theta> (tsubst \<theta>' \<tau>) = tsubst (\<lambda>a. tsubst \<theta> (\<theta>' a)) \<tau>"
proof (induct \<tau> rule: ty.induct)
  case (TyVar a)
  show ?case by simp
next
  case (TyApp c ts)
  then show ?case by (simp add: TyApp.hyps cong: map_cong)
qed

subsection \<open>Operations on terms\<close>

text \<open>Instantiation of type variables occurring in a term.\<close>

fun tinst :: "(name \<Rightarrow> ty) \<Rightarrow> tm \<Rightarrow> tm" where
  "tinst \<theta> (Fv x \<tau>) = Fv x (tsubst \<theta> \<tau>)"
| "tinst \<theta> (Bv i) = Bv i"
| "tinst \<theta> (Cst c \<tau>) = Cst c (tsubst \<theta> \<tau>)"
| "tinst \<theta> (App f a) = App (tinst \<theta> f) (tinst \<theta> a)"
| "tinst \<theta> (Abs \<tau> b) = Abs (tsubst \<theta> \<tau>) (tinst \<theta> b)"

text \<open>
  Substitution for free variables.  No index shifting is needed: substituted terms are
  required to be closed by typing (rule INST), and free variables are never bound by
  @{const Abs}.
\<close>

fun inst_fv :: "(name \<Rightarrow> ty \<Rightarrow> tm) \<Rightarrow> tm \<Rightarrow> tm" where
  "inst_fv \<sigma> (Fv x \<tau>) = \<sigma> x \<tau>"
| "inst_fv \<sigma> (Bv i) = Bv i"
| "inst_fv \<sigma> (Cst c \<tau>) = Cst c \<tau>"
| "inst_fv \<sigma> (App f a) = App (inst_fv \<sigma> f) (inst_fv \<sigma> a)"
| "inst_fv \<sigma> (Abs \<tau> b) = Abs \<tau> (inst_fv \<sigma> b)"

text \<open>
  Beta-instantiation: replace loose index @{term k} by the closed term @{term s} and
  decrement the indices above @{term k}.
\<close>

fun subst_bv :: "nat \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm" where
  "subst_bv k s (Fv x \<tau>) = Fv x \<tau>"
| "subst_bv k s (Bv i) = (if i < k then Bv i else if i = k then s else Bv (i - 1))"
| "subst_bv k s (Cst c \<tau>) = Cst c \<tau>"
| "subst_bv k s (App f a) = App (subst_bv k s f) (subst_bv k s a)"
| "subst_bv k s (Abs \<tau> b) = Abs \<tau> (subst_bv (Suc k) s b)"

text \<open>Abstraction of the free variable @{term "Fv x \<sigma>"} into index @{term k} (closed input).\<close>

fun abs_fv :: "nat \<Rightarrow> name \<Rightarrow> ty \<Rightarrow> tm \<Rightarrow> tm" where
  "abs_fv k x \<sigma> (Fv y \<tau>) = (if y = x \<and> \<tau> = \<sigma> then Bv k else Fv y \<tau>)"
| "abs_fv k x \<sigma> (Bv i) = Bv i"
| "abs_fv k x \<sigma> (Cst c \<tau>) = Cst c \<tau>"
| "abs_fv k x \<sigma> (App f a) = App (abs_fv k x \<sigma> f) (abs_fv k x \<sigma> a)"
| "abs_fv k x \<sigma> (Abs \<tau> b) = Abs \<tau> (abs_fv (Suc k) x \<sigma> b)"

text \<open>Free variables of a term.\<close>

fun fvs :: "tm \<Rightarrow> (name \<times> ty) set" where
  "fvs (Fv x \<tau>) = {(x, \<tau>)}"
| "fvs (Bv i) = {}"
| "fvs (Cst c \<tau>) = {}"
| "fvs (App f a) = fvs f \<union> fvs a"
| "fvs (Abs \<tau> b) = fvs b"

text \<open>Equality @{term "s = t"} at type @{term \<tau>}; @{term \<tau>} is the type of both sides.\<close>

definition mk_eq :: "ty \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm" where
  "mk_eq \<tau> s t = App (App (Cst ''='' (funT \<tau> (funT \<tau> boolT))) s) t"

end
