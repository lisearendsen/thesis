theory syntaxsemantics
imports Main "HOL-Library.Omega_Words_Fun"
begin

datatype 'a regularformula =
  eps | acts "'a set" |
  after "'a regularformula" "'a regularformula"| 
  union "'a regularformula" "'a regularformula" | 
  repeat "'a regularformula"

text \<open>A regular formula is finite if and only if all sets of actions occurring in the 
formula are finite.\<close>

fun finitereg :: "'a regularformula \<Rightarrow> bool" where
"finitereg eps = True" |
"finitereg (acts A) = finite A" |
"finitereg (after R Q) = (finitereg R \<and> finitereg Q)" |
"finitereg (union R Q) = (finitereg R \<and> finitereg Q)" |
"finitereg (repeat R) = finitereg R"

(* from "HOL-Library.Regular-Sets.Regular_Exp" *)
definition concat :: "'a list set \<Rightarrow> 'a list set \<Rightarrow> 'a list set" (infixr \<open>@@\<close> 75) where
"A @@ B = {xs@ys | xs ys. xs:A & ys:B}"

(*this is probably also defined already*)
lemma abinconc : "a \<in> A \<and> b \<in> B \<Longrightarrow> a@b \<in> A@@B"
  using concat_def by blast

lemma exists_abinconc : "(ab \<in> A@@B) = (\<exists>a b. ab = a@b \<and> a \<in> A \<and> b \<in> B)"
  by (simp add: concat_def)

lemma exists_map_abinconc : "(map f ab \<in> A@@B) = (\<exists>a b. ab = a@b \<and> (map f a) \<in> A \<and> (map f b) \<in> B)"
  apply (rule iffI)
  apply (metis exists_abinconc append_eq_map_conv)
  apply (metis abinconc map_append)
  done

text \<open>Define powers on regular formulas to describe the language of the repeat operator.\<close>

overloading
  formpow \<equiv> "compow :: nat \<Rightarrow> 'a list set \<Rightarrow> 'a list set"
begin
  fun formpow :: "nat \<Rightarrow>'a list set \<Rightarrow> 'a list set"
  where
    "formpow 0 A = {[]}" |
    "formpow (Suc n) A = A @@ (formpow n A)"
end

definition formpow :: "nat \<Rightarrow> 'a list set \<Rightarrow> 'a list set" where
  formpow [code_abbrev]: "formpow = compow"

text \<open>Now the language of a regular formula can be defined.\<close>

fun regformtolanguage :: "'a regularformula \<Rightarrow> 'a list set" where
"regformtolanguage eps = {[]}" |
"regformtolanguage (acts A) = {[a] |a. (a \<in>A)}" |
"regformtolanguage (after R Q) = ({r @ q |r q. (r \<in> regformtolanguage R) \<and> (q \<in> regformtolanguage Q)})" |
"regformtolanguage (union R Q) = (regformtolanguage R) \<union> (regformtolanguage Q)" |
"regformtolanguage (repeat R) = (\<Union>n. (regformtolanguage R) ^^ n)"

value "regformtolanguage (eps) :: nat list set" 
value "regformtolanguage (acts {}) :: nat list set" 
value "regformtolanguage (after (acts {1, 2}) (acts {3, 4})) :: nat list set"

text \<open>A mu calculus formula is defined on a type of actions \<open>'a\<close>,
and de Bruijn indices are used as variables.\<close>

datatype 'a formula =
  tt | ff | var nat |
  neg "'a formula" |
  and' "'a formula" "'a formula" | 
  or "'a formula" "'a formula" | 
  box 'a "'a formula" |
  diamond 'a "'a formula" |
  nu "'a formula" |
  mu "'a formula"

value "diamond 2 (box 1 tt) :: nat formula"
value "nu (var 0) :: nat formula "

text \<open>Similarly a labeled transition system is defined on a type of actions \<open>'a\<close> 
and a type of states \<open>'s\<close> (instead of a set of actions and a set of states).
A labeled transition system then consists of a set of transitions and a set of initial states.\<close>

(*maybe remove set of initial states*)
record ('a, 's) lts =
transition :: "('s \<times> 'a \<times> 's) set"
initial :: "'s set"

datatype example_states = s\<^sub>0 | s\<^sub>1
datatype example_actions = \<a> | \<b>

text \<open>A record can be instantiated as follows.\<close>

definition example_lts :: "(example_actions, example_states) lts" where
"example_lts \<equiv> \<lparr>transition = {(s\<^sub>0, \<b>, s\<^sub>1), (s\<^sub>1, \<a>, s\<^sub>0), (s\<^sub>1, \<a>, s\<^sub>1)}, initial = {s\<^sub>0}\<rparr>"

abbreviation newenvironment :: "(nat \<Rightarrow> 's set) \<Rightarrow> 's set \<Rightarrow> (nat \<Rightarrow> 's set) " where
"newenvironment e S' \<equiv> S' ## e"

text \<open>Some simplifications for \<open>newenvironment\<close>.\<close>

lemma newenvironmentsuccessorcomplement [simp] : 
"(newenvironment e S')((Suc i) := - ((newenvironment e S') (Suc i))) = newenvironment (e(i := - e i)) S'"
  apply (rule)
  apply (induct_tac x; simp)
  done

lemma newenvironmentzerocomplement [simp] : 
"(newenvironment e S')(0 := (-(newenvironment e S') 0)) = (newenvironment e (-S'))"
  apply (rule)
  apply (induct_tac x; simp)
  done

lemma newenvironmentswitchsuccessor [simp] : 
"newenvironment (e(i :=  S')) S'' = (newenvironment e S'')((Suc i) := S')"
  apply (rule)
  apply (induct_tac x; simp)
  done

lemma newenvironmentswitchzero [simp] : 
"(newenvironment e S'')(0 := S') = newenvironment e S'"
  apply (rule)
  apply (induct_tac x; simp)
  done

fun formulasemantics :: "'a formula  \<Rightarrow> ('a, 's) lts \<Rightarrow> (nat \<Rightarrow> 's set) \<Rightarrow> 's set" (\<open>\<lbrakk>_\<rbrakk> _ _\<close> [80, 80, 80] 80)
where 
  "\<lbrakk>tt\<rbrakk> M e = UNIV " |
  "\<lbrakk>ff\<rbrakk> M e =  {}" |
  "\<lbrakk>var X\<rbrakk> M e  = e X" |
  "\<lbrakk>neg f\<rbrakk> M e = -(\<lbrakk>f\<rbrakk> M e)" |
  "\<lbrakk>and' f f'\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e \<inter> \<lbrakk>f'\<rbrakk> M e" |
  "\<lbrakk>or f f'\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e \<union> \<lbrakk>f'\<rbrakk> M e" |
  "\<lbrakk>diamond act f\<rbrakk> M e = {s. \<exists> s'. (s, act, s') \<in> (transition M) \<and> s'\<in> \<lbrakk>f\<rbrakk> M e}" |
  "\<lbrakk>box act f\<rbrakk> M e = {s. \<forall> s'. (s, act, s') \<in> (transition M) \<longrightarrow>  s'\<in> \<lbrakk>f\<rbrakk> M e}" |
  "\<lbrakk>nu f\<rbrakk> M e = \<Union> {S'. S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S')}" |
  "\<lbrakk>mu f\<rbrakk> M e = \<Inter> {S'. S' \<supseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S')}"

text \<open>Proving formulas on the example as given before.\<close>

lemma "\<lbrakk>box \<a> ff\<rbrakk> example_lts e = {s\<^sub>0}"
  apply (simp add: example_lts_def)
  using example_states.exhaust apply auto
  done

lemma "\<lbrakk>nu (diamond \<a> (var 0))\<rbrakk> example_lts e = {s\<^sub>1}"
proof-
  have "\<forall>S'. S' \<subseteq> {s. \<exists>s'. ((s = s\<^sub>1 \<and> s' = s\<^sub>0) \<or> (s = s\<^sub>1 \<and> s' = s\<^sub>1)) \<and> s' \<in> S'} = (S' = {} \<or> S' = {s\<^sub>1})" using example_states.exhaust by auto
  hence "\<Union> {S'. S' \<subseteq> {s. \<exists>s'. ((s = s\<^sub>1 \<and> s' = s\<^sub>0) \<or> (s = s\<^sub>1 \<and> s' = s\<^sub>1)) \<and> s' \<in> S'}} = {s\<^sub>1}" by auto
  thus ?thesis by (simp add: example_lts_def)
qed

lemma "\<lbrakk>nu (diamond \<a> (var 0))\<rbrakk> example_lts e = {s\<^sub>1}"
  apply (simp add: example_lts_def)
  apply (rule equalityI)
  apply blast
  apply (rule Union_upper)
  apply auto
  done

fun shiftup :: "'a formula \<Rightarrow> nat \<Rightarrow> 'a formula "
where 
  "(shiftup tt i) = tt " |
  "(shiftup ff i) = ff" |
  "(shiftup (var X) i)  = (if X < i then var X else var (X + 1))" |
  "(shiftup (neg f) i) = neg (shiftup f i)" |
  "(shiftup (and' f f') i) = and' (shiftup f i) (shiftup f' i) " |
  "(shiftup (or f f') i) = or (shiftup f i) (shiftup f' i)" |
  "(shiftup (diamond act f) i) = diamond act (shiftup f i)" |
  "(shiftup (box act f) i) = box act (shiftup f i)" |
  "(shiftup (nu f) i) = nu (shiftup f (Suc i))" |
  "(shiftup (mu f) i) = mu (shiftup f (Suc i))"

fun shiftdown :: "'a formula \<Rightarrow> nat \<Rightarrow> 'a formula "
where 
  "(shiftdown tt i) = tt " |
  "(shiftdown ff i) = ff" |
  "(shiftdown (var X) i)  = (if X \<le> i then var X else var (X - 1))" |
  "(shiftdown (neg f) i) = neg (shiftdown f i)" |
  "(shiftdown (and' f f') i) = and' (shiftdown f i) (shiftdown f' i) " |
  "(shiftdown (or f f') i) = or (shiftdown f i) (shiftdown f' i)" |
  "(shiftdown (diamond act f) i) = diamond act (shiftdown f i) " |
  "(shiftdown (box act f) i) = box act (shiftdown f i)" |
  "(shiftdown (nu f) i) = nu (shiftdown f (Suc i))" |
  "(shiftdown (mu f) i) = mu (shiftdown f (Suc i))"

lemma shiftupanddown : "shiftdown (shiftup f i) i = f"
  by (induct f arbitrary : i; simp)

definition shiftdownenv :: "(nat \<Rightarrow> 's set) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 's set) " where
"shiftdownenv e i n = (if n < i then e n else e (n + 1))"

fun Andlist :: "'a list \<Rightarrow> ('a \<Rightarrow> 'a formula) \<Rightarrow> 'a formula " where
"Andlist [] F = tt" |
"Andlist (a # as) F = and' (F a) (Andlist as F)"

definition And :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a formula) \<Rightarrow> 'a formula" where
"And A F = Andlist (if finite A then (SOME listA. set listA = A) else undefined) F"

lemma Andlist_eq_all : "\<lbrakk>Andlist Alist F\<rbrakk> M e = {s. \<forall>a \<in> set Alist. s \<in> \<lbrakk>F a\<rbrakk> M e}"
  by (induct Alist; simp; auto)

lemma And_eq_all : "finite A \<Longrightarrow> \<lbrakk>And A F\<rbrakk> M e = {s. \<forall>a \<in> A. s \<in> \<lbrakk>F a\<rbrakk> M e}"
  apply (simp add: And_def Andlist_eq_all)
  apply (rule someI2_ex; simp add: finite_list)
  done

lemma And_eq_all' [simp] : "finite A \<Longrightarrow> \<lbrakk>And A F\<rbrakk> M e = (\<Inter>a \<in> A. {s. s \<in> \<lbrakk>F a\<rbrakk> M e})"
  by (subst And_eq_all; simp; auto)

fun Orlist :: "'a list \<Rightarrow> ('a \<Rightarrow> 'a formula) \<Rightarrow> 'a formula " where
"Orlist [] F = ff" |
"Orlist (a # as) F = or (F a) (Orlist as F)"

definition Or :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a formula) \<Rightarrow> 'a formula" where
"Or A F = Orlist (if finite A then (SOME listA. set listA = A) else undefined) F"

lemma Orlist_eq_exist : "\<lbrakk>Orlist Alist F\<rbrakk> M e = {s. \<exists>a \<in> set Alist. s \<in> \<lbrakk>F a\<rbrakk> M e}"
  by (induct Alist; auto)

lemma Or_eq_exist : "finite A \<Longrightarrow> \<lbrakk>Or A F\<rbrakk> M e = {s. \<exists>a \<in> A. s \<in> \<lbrakk>F a\<rbrakk> M e}"
  apply (simp add: Or_def Orlist_eq_exist)
  apply (rule someI2_ex; simp add: finite_list)
  done

lemma Or_eq_all' : "finite A \<Longrightarrow> \<lbrakk>Or A F\<rbrakk> M e = (\<Union>a \<in> A. {s. s \<in> \<lbrakk>F a\<rbrakk> M e})"
  by (subst Or_eq_exist; auto)

fun Diamondlist :: "'a list \<Rightarrow> 'a formula \<Rightarrow> 'a formula " where
"Diamondlist [] f = ff" |
"Diamondlist (a # as) f = or (diamond a f) (Diamondlist as f)"

fun Diamond :: "'a regularformula \<Rightarrow> 'a formula \<Rightarrow> 'a formula " where 
"Diamond eps f = f" |
"Diamond (acts A) f = Diamondlist (if finite A then (SOME listA. set listA = A) else undefined) f" |
"Diamond (after R Q) f = Diamond R (Diamond Q f)" |
"Diamond (union R Q) f = or (Diamond R f) (Diamond Q f)" |
"Diamond (repeat R) f =  mu (or (Diamond R (var 0)) (shiftup f 0))" 

lemma Diamondlist_eq_exist : "\<lbrakk>Diamondlist A f\<rbrakk> M e = {s. \<exists> s' act. act \<in> set A \<and> (s, act, s') \<in> (transition M) \<and> s' \<in> \<lbrakk>f\<rbrakk> M e}"
  by (induct A; simp; auto)

lemma Diamond_eq_exist [simp] : "finite A \<Longrightarrow>
\<lbrakk>Diamond (acts A) f\<rbrakk> M e = {s. \<exists> s' act. act \<in> A \<and> (s, act, s') \<in> (transition M) \<and> s' \<in> \<lbrakk>f\<rbrakk> M e}"
  apply (simp add: Diamondlist_eq_exist)
  apply (rule someI2_ex; simp add: finite_list)
  done

lemma shiftuptwice : "m \<le> i \<Longrightarrow> shiftup (shiftup f m) (Suc i) = shiftup (shiftup f i) m"
  by (induct f arbitrary : i m; simp)

lemma shiftupDiamondlist [simp] : "shiftup (Diamondlist Alist f) i = Diamondlist Alist (shiftup f i)"
  by (induct Alist; simp)

lemma shiftupDiamond [simp] : "finitereg R \<Longrightarrow> shiftup (Diamond R f) i = Diamond R (shiftup f i)"
  by (induction R arbitrary : i f; simp add: shiftuptwice)

lemma shiftupdown : "m \<le> i \<Longrightarrow> shiftdown (shiftup f m) (Suc i) = shiftup (shiftdown f i) m"
  by (induct f arbitrary : i m; simp; arith)

lemma shiftdownDiamondlist [simp] : "shiftdown (Diamondlist Alist f) i = Diamondlist Alist (shiftdown f i)"
  by (induct Alist; simp)

lemma shiftdownDiamond [simp] : "finitereg R \<Longrightarrow> shiftdown (Diamond R f) i = Diamond R (shiftdown f i)"
  by (induction R arbitrary : i f; simp add: shiftupdown)

fun Boxlist :: "'a list \<Rightarrow> 'a formula \<Rightarrow> 'a formula " where
"Boxlist [] f = tt" |
"Boxlist (a # as) f = and' (box a f) (Boxlist as f)"

fun Box :: "'a regularformula \<Rightarrow> 'a formula \<Rightarrow> 'a formula " where 
"Box eps f = f" |
"Box (acts A) f = Boxlist (if finite A then (SOME listA. set listA = A) else []) f" |
"Box (after R Q) f = Box R (Box Q f)" |
"Box (union R Q) f = and' (Box R f) (Box Q f)" |
"Box (repeat R) f =  nu (and' (Box R (var 0)) (shiftup f 0))" 

lemma Boxlist_eq_forall : "\<lbrakk>Boxlist A f\<rbrakk> M e = {s. \<forall> s' act. act \<in> set A \<and> (s, act, s') \<in> (transition M) \<longrightarrow> s' \<in> \<lbrakk>f\<rbrakk> M e}"
  by (induct A; simp; auto)

lemma Box_eq_forall [simp] : "finite A \<Longrightarrow>
\<lbrakk>Box (acts A) f\<rbrakk> M e = {s. \<forall> s' act. act \<in> A \<and> (s, act, s') \<in> (transition M) \<longrightarrow> s' \<in> \<lbrakk>f\<rbrakk> M e}"
  apply (simp add: Boxlist_eq_forall)
  apply (rule someI2_ex; simp add: finite_list)
  done

lemma shiftupBoxlist [simp] : "shiftup (Boxlist Alist f) i = Boxlist Alist (shiftup f i)"
  by (induct Alist; simp)

lemma shiftupBox : "finitereg R \<Longrightarrow> shiftup (Box R f) i = Box R (shiftup f i)"
  by (induction R arbitrary : i f; simp add: shiftuptwice)

lemma shiftdownBoxlist [simp] : "shiftdown (Boxlist Alist f) i = Boxlist Alist (shiftdown f i)"
  by (induct Alist; simp)

lemma shiftdownBox [simp] : "finitereg R \<Longrightarrow> shiftdown (Box R f) i = Box R (shiftdown f i)"
  by (induction R arbitrary : i f; simp add: shiftupdown)

fun negvari :: "'a formula \<Rightarrow> nat \<Rightarrow> 'a formula "
where 
  "(negvari tt i) = tt " |
  "(negvari ff i) = ff" |
  "(negvari (var X) i)  = (if i = X then (neg (var X)) else (var X))" |
  "(negvari (neg f) i) = neg (negvari f i)" |
  "(negvari (and' f f') i) = and' (negvari f i) (negvari f' i) " |
  "(negvari (or f f') i) = or (negvari f i) (negvari f' i)" |
  "(negvari (diamond act f) i) = diamond act (negvari f i) " |
  "(negvari (box act f) i) = box act (negvari f i)" |
  "(negvari (nu f) i) = nu (negvari f (Suc i))" |
  "(negvari (mu f) i) = mu (negvari f (Suc i))"

lemma negvarishiftup : "m \<le> i \<Longrightarrow> negvari (shiftup f m) (Suc i) = shiftup (negvari f i) m"
  by (induct f arbitrary : m i; simp)

lemma negvariDiamondlist [simp] : "negvari (Diamondlist Alist f) i = Diamondlist Alist (negvari f i)"
  by (induct Alist; simp)

lemma negvariDiamond [simp] : "finitereg R \<Longrightarrow> negvari (Diamond R f) i = Diamond R (negvari f i)"
  by (induct R arbitrary : f i; simp add : negvarishiftup)

lemma negvariBoxlist [simp] : "negvari (Boxlist Alist f) i = Boxlist Alist (negvari f i)"
  by (induct Alist; simp)

lemma negvariBox [simp] : "finitereg R \<Longrightarrow> negvari (Box R f) i = Box R (negvari f i)"
  by (induct R arbitrary : f i; simp add : negvarishiftup)

value "negvari (or (var 0) (mu (and' (var 0) (var 1)))) 0 :: nat formula"

section \<open>negate formulas\<close>

lemma negtrue [simp] : "\<lbrakk>neg tt\<rbrakk> M e = \<lbrakk>ff\<rbrakk> M e"
  by simp

lemma negfalse [simp]: "\<lbrakk>neg ff\<rbrakk> M e = \<lbrakk>tt\<rbrakk> M e"
  by simp

lemma negnegf [simp] : "\<lbrakk>neg (neg (f))\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e"
  by simp

lemma negand' [simp] : "\<lbrakk>neg (and' f f')\<rbrakk> M e = \<lbrakk>or (neg f) (neg f')\<rbrakk> M e"
  by simp

lemma negor [simp] : "\<lbrakk>neg (or f f')\<rbrakk> M e = \<lbrakk>and' (neg f) (neg f')\<rbrakk> M e"
  by simp

lemma negbox : "\<lbrakk>neg (box act f)\<rbrakk> M e = \<lbrakk>diamond act (neg f)\<rbrakk> M e"
  by auto

lemma negdiamond : "\<lbrakk>neg (diamond act f)\<rbrakk> M e = \<lbrakk>box act (neg f)\<rbrakk> M e"
  by auto

lemma movenegvariin : "\<lbrakk>f\<rbrakk> M (e(i := -e(i))) = \<lbrakk>negvari f i\<rbrakk> M e"
  apply (induct f arbitrary : e i; simp; subgoal_tac "\<And>S'. \<lbrakk>f\<rbrakk> M (newenvironment e S') (Suc i := - e i) = \<lbrakk>negvari f (Suc i)\<rbrakk> M (newenvironment e S')")
  apply simp
  prefer 2 apply simp
proof-
  fix f e i S'
  assume "\<And>e i. \<lbrakk>f\<rbrakk> M e(i := - e i) = \<lbrakk>negvari f i\<rbrakk> M e"
  hence "\<lbrakk>f\<rbrakk> M ((newenvironment e S') (Suc i := - (newenvironment e S' (Suc i)))) = \<lbrakk>negvari f (Suc i)\<rbrakk> M (newenvironment e S')" by metis
  moreover have "\<lbrakk>f\<rbrakk> M ((newenvironment e S') (Suc i := - (newenvironment e S' (Suc i)))) = \<lbrakk>f\<rbrakk> M ((newenvironment e S') (Suc i := - e i))" by simp
  ultimately show "\<lbrakk>f\<rbrakk> M (newenvironment e S') (Suc i := - e i) = \<lbrakk>negvari f (Suc i)\<rbrakk> M (newenvironment e S')" by simp
  thus " \<lbrakk>f\<rbrakk> M (newenvironment e S') (Suc i := - e i) = \<lbrakk>negvari f (Suc i)\<rbrakk> M (newenvironment e S')" by simp
qed

lemma pushnegnu : "\<lbrakk>neg (nu f)\<rbrakk> M e = \<Inter> {S. S \<supseteq> \<lbrakk>neg f\<rbrakk> M (newenvironment e (-S))}"
proof-
  have "- \<Union> {S'. S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S')} = \<Inter> {-S'| S'. S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S')}" by blast
  moreover have "... = \<Inter> {S'. -S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e (-S'))}" using double_compl by metis
  moreover have "... = \<Inter> {S. S \<supseteq> \<lbrakk>neg f\<rbrakk> M (newenvironment e (-S))}" by auto
  ultimately show ?thesis by simp
qed

lemma negnu : "\<lbrakk>neg (nu f)\<rbrakk> M e = \<lbrakk>mu (neg (negvari f 0))\<rbrakk> M e"
proof-
  have "\<And> S'. \<lbrakk>neg f\<rbrakk> M (newenvironment e (-S')) = \<lbrakk>negvari (neg f) 0\<rbrakk> M (newenvironment e S')" using movenegvariin newenvironmentzerocomplement by metis  
  hence "\<Inter> {S'. S' \<supseteq> \<lbrakk>neg f\<rbrakk> M (newenvironment e (-S'))} = \<Inter> {S'. S' \<supseteq> \<lbrakk>neg (negvari f 0)\<rbrakk> M (newenvironment e S')}" by auto
  moreover have "\<lbrakk>neg (nu f)\<rbrakk> M e = (\<Inter> {S'. S' \<supseteq> \<lbrakk>neg f\<rbrakk> M (newenvironment e (-S'))})" using pushnegnu by metis
  ultimately show ?thesis by auto
qed

lemma negvarnegvar [simp] : "\<lbrakk>(negvari (negvari f i) i)\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e"
  by (induct f arbitrary : i e; simp)

lemma negmu : "\<lbrakk>(neg (mu f))\<rbrakk> M e = \<lbrakk>(nu (neg (negvari f 0)))\<rbrakk> M e"
proof-
  have "\<lbrakk>mu (neg (negvari (neg (negvari f 0)) 0))\<rbrakk> M e = \<lbrakk>neg (nu (neg (negvari f 0)))\<rbrakk> M e" by (simp only: negnu)
  hence "\<lbrakk>neg (mu (neg (negvari (neg (negvari f 0)) 0)))\<rbrakk> M e = \<lbrakk>neg (neg (nu (neg (negvari f 0))))\<rbrakk> M e" by auto
  thus ?thesis by simp
qed

fun occursvari :: "'a formula \<Rightarrow> nat \<Rightarrow> bool "
where 
  "(occursvari tt i) = False " |
  "(occursvari ff i) = False" |
  "(occursvari (var X) i) = (i = X)" |
  "(occursvari (neg f) i) = (occursvari f i)" |
  "(occursvari (and' f f') i) = ((occursvari f i) \<or> (occursvari f' i))" |
  "(occursvari (or f f') i) = ((occursvari f i) \<or> (occursvari f' i))" |
  "(occursvari (diamond act f) i) = (occursvari f i) " |
  "(occursvari (box act f) i) = (occursvari f i)" |
  "(occursvari (nu f) i) = (occursvari f (Suc i))" |
  "(occursvari (mu f) i) = (occursvari f (Suc i))"

fun emptyreg :: "'a regularformula \<Rightarrow> bool" where
  "emptyreg eps = False" | 
  "emptyreg (acts A) = (A = {})" |
  "emptyreg (after R Q) = (emptyreg R \<or> emptyreg Q)" |
  "emptyreg (union R Q) = (emptyreg R \<and> emptyreg Q)" | 
  "emptyreg (repeat R) = False"

lemma emptyregdef : "emptyreg R = (regformtolanguage R = {})"
  apply (induct R; simp)
  apply blast
  using formpow.simps apply blast
  done

lemma occursvarishiftup : "m \<le> i \<Longrightarrow> occursvari (shiftup f m) (Suc i) = occursvari f i"
  by (induct f arbitrary : i m; simp)

lemma occursDiamondlist [simp] : "occursvari (Diamondlist Alist f) i = (occursvari f i \<and> \<not>(Alist = []))"
  by (induct Alist arbitrary : f i; simp; blast)

lemma occursDiamond [simp] : "finitereg R \<Longrightarrow> (occursvari (Diamond R f) i) = (occursvari f i \<and> \<not>emptyreg R)"
  apply (induct R arbitrary : f i; simp add : occursvarishiftup)
  apply (rule someI2_ex)
  apply (simp add: finite_list)
  apply auto
  done

lemma occursBoxlist [simp] : "occursvari (Boxlist Alist f) i = (occursvari f i \<and> \<not>(Alist = []))"
  by (induct Alist arbitrary : f i; simp; blast)

lemma occursBox [simp] : "finitereg R \<Longrightarrow> (occursvari (Box R f) i) = (occursvari f i \<and> \<not>emptyreg R)"
  apply (induct R arbitrary : f i; simp add : occursvarishiftup)
  apply (rule someI2_ex)
  apply (simp add: finite_list)
  apply auto
  done

lemma notoccursnuandmu [simp] :
assumes "\<forall>i e. \<not> occursvari (f :: 'a formula) i \<longrightarrow> (\<lbrakk>f\<rbrakk> M e = \<lbrakk>f\<rbrakk> M (e(i := S')))" 
shows "\<sigma> \<in> {nu, mu} \<Longrightarrow>  \<not> occursvari (\<sigma> f) i \<longrightarrow> (\<lbrakk>\<sigma> f\<rbrakk> M e = \<lbrakk>\<sigma> f\<rbrakk> M (e(i := S')))"
proof
  assume assum1 : "(\<sigma> :: ('a formula => 'a formula)) \<in> {nu, mu}"
  assume assum2: "\<not> occursvari (\<sigma> f) i"
  hence "\<not> occursvari f (Suc i)" using assum1 by (cases "\<sigma> = mu") simp_all      
  hence "(\<forall> S''. \<lbrakk>f\<rbrakk> M (newenvironment e S'') = \<lbrakk>f\<rbrakk> M ((newenvironment e S'') ((Suc i) := S')))" using assms by metis
  hence con1: "\<forall> S''. \<lbrakk>f\<rbrakk> M (newenvironment e S'') = \<lbrakk>f\<rbrakk> M (newenvironment (e(i := S')) S'')" by simp
  show "(\<lbrakk>\<sigma> f\<rbrakk> M e = \<lbrakk>\<sigma> f\<rbrakk> M (e(i := S')))"
    apply (cases "\<sigma> = mu")
    apply (simp add: con1) 
    apply (subgoal_tac "\<sigma> = nu")
    apply (simp add: con1) 
    using assum1 apply blast
    done
qed

lemma notoccurs [simp] : "(\<not>(occursvari f i) \<longrightarrow> (\<lbrakk>f\<rbrakk> M e = \<lbrakk>f\<rbrakk> M (e(i := S'))))"
  apply (induct f arbitrary: e i S')
  prefer 9
  using notoccursnuandmu apply blast
  prefer 9
  using notoccursnuandmu apply blast
  apply (simp_all)
  done

lemma notoccurseqnu :
  assumes "\<not> occursvari f 0"
  shows "\<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>nu f\<rbrakk> M e"
  apply simp
proof-
  have "\<forall>S''. \<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>f\<rbrakk> M ((newenvironment e S') (0 := S''))" using assms notoccurs by metis
  hence "\<forall>S''. \<lbrakk>f\<rbrakk> M ((newenvironment e S'')) = \<lbrakk>f\<rbrakk> M (newenvironment e S')" using newenvironmentswitchzero by auto
  hence "\<Union> {S''. S'' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S'')} = \<Union> {S''. S'' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S')}" by blast
  moreover have "... = \<lbrakk>f\<rbrakk> M (newenvironment e S')" by auto
  ultimately show "\<lbrakk>f\<rbrakk> M (newenvironment e S') = \<Union> {S'. S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S')}" by auto
qed

lemma notoccurseqmu :
  assumes "\<not> occursvari f 0"
  shows "\<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>mu f\<rbrakk> M e"
  apply simp
proof-
  have "\<forall>S''. \<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>f\<rbrakk> M ((newenvironment e S') (0 := S''))" using assms notoccurs by metis
  hence "\<forall>S''. \<lbrakk>f\<rbrakk> M ((newenvironment e S'')) = \<lbrakk>f\<rbrakk> M (newenvironment e S')" using newenvironmentswitchzero by auto
  hence "\<Inter> {S''. \<lbrakk>f\<rbrakk> M (newenvironment e S'') \<subseteq> S''} = \<Inter> {S''. \<lbrakk>f\<rbrakk> M (newenvironment e S') \<subseteq> S''}" by blast
  moreover have "... = \<lbrakk>f\<rbrakk> M (newenvironment e S')" by auto
  ultimately show "\<lbrakk>f\<rbrakk> M (newenvironment e S') = \<Inter> {S'. \<lbrakk>f\<rbrakk> M (newenvironment e S') \<subseteq> S'}" by auto
qed

definition transformer :: "'a formula \<Rightarrow> ('a, 's) lts \<Rightarrow> (nat \<Rightarrow> 's set) \<Rightarrow> 's set \<Rightarrow> 's set "
  where
"transformer f M e S' = \<lbrakk>f\<rbrakk> M (newenvironment e S')"

definition dependvari :: "'a formula \<Rightarrow> ('a, 's) lts \<Rightarrow> nat \<Rightarrow> bool" where
"dependvari f M i = (\<exists>e S'. \<lbrakk>f\<rbrakk> M e \<noteq> \<lbrakk>f\<rbrakk> M (e(i := S')))"

lemma transformerdef : "transformer f M e = (\<lambda>S'. \<lbrakk>f\<rbrakk> M (newenvironment e S'))"
  by (meson transformer_def)

lemma notdependsmono : "\<not>dependvari f M i \<Longrightarrow>
  mono (\<lambda>S.(\<lbrakk>f\<rbrakk> M (e(i := S)))) \<and> antimono (\<lambda>S.(\<lbrakk>f\<rbrakk> M (e(i := S))))"
  by (induct f arbitrary: i; simp add: dependvari_def monotone_def)

lemma notdependscoro : "(\<not>dependvari f M 0 \<longrightarrow> mono (transformer f M e))"
  apply (simp add: transformerdef)
proof-
  have "\<forall>S''. \<not>dependvari f M 0 \<longrightarrow> mono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M ((newenvironment e S'')(0 := S'))))" using notdependsmono by metis
  thus "\<not>dependvari f M 0 \<longrightarrow> mono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M (newenvironment e S')))" by auto
qed

lemma andsubset : 
  assumes "A\<^sub>1 \<subseteq> B\<^sub>1 \<and> A\<^sub>2 \<subseteq> B\<^sub>2"
  shows "A\<^sub>1 \<inter> A\<^sub>2 \<subseteq> B\<^sub>1 \<and> A\<^sub>1 \<inter> A\<^sub>2 \<subseteq> B\<^sub>2"
  using assms by auto

lemma orsubset : 
  assumes "A\<^sub>1 \<subseteq> B\<^sub>1 \<or> A\<^sub>2 \<subseteq> B\<^sub>2"
  shows "A\<^sub>1 \<subseteq> B\<^sub>1 \<union> B\<^sub>2 \<or> A\<^sub>2 \<subseteq> B\<^sub>1 \<union> B\<^sub>2"
  using assms by auto

fun notdependalloccursposnegi :: "'a formula \<Rightarrow> ('a ,'s) lts \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool"
where 
  "(notdependalloccursposnegi tt M i b) = True " |
  "(notdependalloccursposnegi ff M i b) = True" |
  "(notdependalloccursposnegi (var X) M i b) = ((X \<noteq> i) \<or> b)" |
  "(notdependalloccursposnegi (neg f) M i b) = (\<not>dependvari f M i \<or> notdependalloccursposnegi f M i (\<not>b))" |
  "(notdependalloccursposnegi (and' f f') M i b) = (\<not>dependvari (and' f f') M i \<or> (notdependalloccursposnegi f M i b \<and> notdependalloccursposnegi f' M i b))" |
  "(notdependalloccursposnegi (or f f') M i b) = (\<not>dependvari (or f f') M i \<or> (notdependalloccursposnegi f M i b \<and> notdependalloccursposnegi f' M i b))" |
  "(notdependalloccursposnegi (diamond act f) M i b) = (\<not>dependvari (diamond act f) M i \<or> notdependalloccursposnegi f M i b) " |
  "(notdependalloccursposnegi (box act f) M i b) = (\<not>dependvari (box act f) M i \<or> notdependalloccursposnegi f M i b)" |
  "(notdependalloccursposnegi (nu f) M i b) = (\<not>dependvari (nu f) M i \<or> notdependalloccursposnegi f M (Suc i) b)" |
  "(notdependalloccursposnegi (mu f) M i b) = (\<not>dependvari (mu f) M i \<or> notdependalloccursposnegi f M (Suc i) b)"

lemma notoccursposneg : "\<not>occursvari f i \<Longrightarrow> notdependalloccursposnegi f M i True \<and> notdependalloccursposnegi f M i False"
  by (induct f arbitrary: i; simp)

lemma dependvarineg : "dependvari f M i = dependvari (neg f) M i"
  by (simp add: dependvari_def)

lemma notdepends : "\<not>dependvari f M i \<Longrightarrow> notdependalloccursposnegi f M i b"
  apply (induct f arbitrary : i b; simp add: dependvari_def)
  apply (rule impI)
  apply (subgoal_tac "{} = UNIV")
  apply auto
  done

lemma andormono : 
  assumes "mono f1 \<and> mono f2"
  shows "mono (\<lambda>S'. f1 S' \<inter> f2 S')"
  and "mono (\<lambda>S'. f1 S' \<union> f2 S')"
  apply (simp_all add: monotone_def)
  apply (metis assms andsubset monotone_def)
  apply (metis assms orsubset monotone_def)
  done

lemma andorantimono : 
  assumes "antimono f1 \<and> antimono f2"
  shows "antimono (\<lambda>S'. f1 S' \<inter> f2 S')"
  and "antimono (\<lambda>S'. f1 S' \<union> f2 S')"
  apply (simp_all add: monotone_def)
  apply (metis assms andsubset monotone_def)
  apply (metis assms orsubset monotone_def)
  done

lemma boxdiamondmono : 
  assumes "mono f"
  shows "mono (\<lambda>S'. {s. \<forall> s'. (s, a, s') \<in> (transition M) \<longrightarrow>  s' \<in> f S'})"
  and "mono (\<lambda>S'. {s. \<exists> s'. (s, a, s') \<in> (transition M) \<and>  s' \<in> f S'})"
  apply (simp_all add: monotone_def)
  using assms monoD apply blast+
  done

lemma boxdiamondantimono : 
  assumes "antimono f"
  shows "antimono (\<lambda>S'. {s. \<forall> s'. (s, a, s') \<in> (transition M) \<longrightarrow>  s' \<in> f S'})"
  and "antimono (\<lambda>S'. {s. \<exists> s'. (s, a, s') \<in> (transition M) \<and>  s' \<in> f S'})"
  apply (simp_all add: monotone_def)
  using assms antimonoD apply (blast)+
  done

lemma numumono : 
  assumes "\<And>S''. mono (f S'')"
  shows "mono (\<lambda>S'. (\<Union> {S''. S'' \<subseteq> f S'' S'}))"
  and "mono (\<lambda>S'. (\<Inter> {S''. S'' \<supseteq> f S'' S'}))"
  apply (simp_all add: monotone_def)
  apply (rule allI)+
  apply (rule impI)
  apply (subgoal_tac "\<forall>S''. S'' \<subseteq> f S'' x \<longrightarrow> S'' \<subseteq> f S'' y")
  apply blast
  using assms monotoneD apply fastforce
  apply (rule allI)+
  apply (rule impI)
  apply (subgoal_tac "\<forall>S''. f S'' y \<subseteq> S'' \<longrightarrow> f S'' x \<subseteq> S''")
  apply blast
  using assms monotoneD apply fastforce
  done

lemma numuantimono : 
  assumes "\<And>S''. antimono (f S'')"
  shows "antimono (\<lambda>S'. (\<Union> {S''. S'' \<subseteq> f S'' S'}))"
  and "antimono (\<lambda>S'. (\<Inter> {S''. S'' \<supseteq> f S'' S'}))"
  apply (simp_all add: monotone_def)
  apply (rule allI)+
  apply (rule impI)
  apply (subgoal_tac "\<forall>S''. S'' \<subseteq> f S'' y \<longrightarrow> S'' \<subseteq> f S'' x")
  apply blast
  using assms monotoneD apply fastforce
  apply (rule allI)+
  apply (rule impI)
  apply (subgoal_tac "\<forall>S''. f S'' x \<subseteq> S'' \<longrightarrow> f S'' y \<subseteq> S''")
  apply blast
  using assms monotoneD apply fastforce
  done

lemma monotonicitynotdepend :
"(notdependalloccursposnegi f M i True \<longrightarrow> mono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M (e(i := S')))))
 \<and> (notdependalloccursposnegi f M i False \<longrightarrow> antimono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M (e(i := S')))))"
  apply (induct f arbitrary : i e; simp only: notdependalloccursposnegi.simps)
  apply (simp add: monotone_def)+
  apply (metis notdepends)
proof-
  fix f1 f2 i e
  assume assum1: "(\<And>i e. (notdependalloccursposnegi f1 M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>f1\<rbrakk> M e(i := S'))) \<and> (notdependalloccursposnegi f1 M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>f1\<rbrakk> M e(i := S'))))"
  assume assum2: "(\<And>i e. (notdependalloccursposnegi f2 M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>f2\<rbrakk> M e(i := S'))) \<and> (notdependalloccursposnegi f2 M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>f2\<rbrakk> M e(i := S'))))"
  have "\<not> dependvari (and' f1 f2) M i \<longrightarrow> (mono (\<lambda>S'. \<lbrakk>and' f1 f2\<rbrakk> M e(i := S')) \<and> antimono (\<lambda>S'. \<lbrakk>and' f1 f2\<rbrakk> M e(i := S')))" using notdependsmono by metis
  moreover have "notdependalloccursposnegi f1 M i True \<and> notdependalloccursposnegi f2 M i True \<Longrightarrow> mono (\<lambda>S'. \<lbrakk>and' f1 f2\<rbrakk> M e(i := S'))" by (auto simp: assum1 assum2 andormono)
  moreover have "notdependalloccursposnegi f1 M i False \<and> notdependalloccursposnegi f2 M i False \<Longrightarrow> antimono (\<lambda>S'. \<lbrakk>and' f1 f2\<rbrakk> M e(i := S'))" by (auto simp: assum1 assum2 andorantimono)
  ultimately show "(\<not> dependvari (and' f1 f2) M i \<or> notdependalloccursposnegi f1 M i True \<and> notdependalloccursposnegi f2 M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>and' f1 f2\<rbrakk> M e(i := S'))) \<and> (\<not> dependvari (and' f1 f2) M i \<or> notdependalloccursposnegi f1 M i False \<and> notdependalloccursposnegi f2 M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>and' f1 f2\<rbrakk> M e(i := S')))" by auto
  have "\<not> dependvari (or f1 f2) M i \<longrightarrow> (mono (\<lambda>S'. \<lbrakk>or f1 f2\<rbrakk> M e(i := S')) \<and> antimono (\<lambda>S'. \<lbrakk>or f1 f2\<rbrakk> M e(i := S')))" using notdependsmono by metis
  moreover have "notdependalloccursposnegi f1 M i True \<and> notdependalloccursposnegi f2 M i True \<Longrightarrow> mono (\<lambda>S'. \<lbrakk>or f1 f2\<rbrakk> M e(i := S'))" by (auto simp: assum1 assum2 andormono)
  moreover have "notdependalloccursposnegi f1 M i False \<and> notdependalloccursposnegi f2 M i False \<Longrightarrow> antimono (\<lambda>S'. \<lbrakk>or f1 f2\<rbrakk> M e(i := S'))" by (auto simp: assum1 assum2 andorantimono)
  ultimately show "(\<not> dependvari (or f1 f2) M i \<or> notdependalloccursposnegi f1 M i True \<and> notdependalloccursposnegi f2 M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>or f1 f2\<rbrakk> M e(i := S'))) \<and> (\<not> dependvari (or f1 f2) M i \<or> notdependalloccursposnegi f1 M i False \<and> notdependalloccursposnegi f2 M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>or f1 f2\<rbrakk> M e(i := S')))" by auto
next
  fix a f i e
  assume assum1: "(\<And>i e. (notdependalloccursposnegi f M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>f\<rbrakk> M e(i := S'))) \<and> (notdependalloccursposnegi f M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>f\<rbrakk> M e(i := S'))))"
  have "\<not> dependvari (box a f) M i \<longrightarrow> (mono (\<lambda>S'. \<lbrakk>box a f\<rbrakk> M e(i := S')) \<and> antimono (\<lambda>S'. \<lbrakk>box a f\<rbrakk> M e(i := S')))" using notdependsmono by metis
  moreover have "notdependalloccursposnegi f M i True \<Longrightarrow> mono (\<lambda>S'. \<lbrakk>box a f\<rbrakk> M e(i := S'))" by (auto simp: assum1 boxdiamondmono)
  moreover have "notdependalloccursposnegi f M i False \<Longrightarrow> antimono (\<lambda>S'. \<lbrakk>box a f\<rbrakk> M e(i := S'))" by (auto simp: assum1 boxdiamondantimono)
  ultimately show "(\<not> dependvari (box a f) M i \<or> notdependalloccursposnegi f M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>box a f\<rbrakk> M e(i := S'))) \<and> (\<not> dependvari (box a f) M i \<or> notdependalloccursposnegi f M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>box a f\<rbrakk> M e(i := S')))" by auto
  have "\<not> dependvari (diamond a f) M i \<longrightarrow> (mono (\<lambda>S'. \<lbrakk>diamond a f\<rbrakk> M e(i := S')) \<and> antimono (\<lambda>S'. \<lbrakk>diamond a f\<rbrakk> M e(i := S')))" using notdependsmono by metis
  moreover have "notdependalloccursposnegi f M i True \<Longrightarrow> mono (\<lambda>S'. \<lbrakk>diamond a f\<rbrakk> M e(i := S'))" by (auto simp: assum1 boxdiamondmono)
  moreover have "notdependalloccursposnegi f M i False \<Longrightarrow> antimono (\<lambda>S'. \<lbrakk>diamond a f\<rbrakk> M e(i := S'))" by (auto simp: assum1 boxdiamondantimono)
  ultimately show "(\<not> dependvari (diamond a f) M i \<or> notdependalloccursposnegi f M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>diamond a f\<rbrakk> M e(i := S'))) \<and> (\<not> dependvari (diamond a f) M i \<or> notdependalloccursposnegi f M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>diamond a f\<rbrakk> M e(i := S')))" by auto
next
  fix f i e
  assume assum1: "(\<And>i e. (notdependalloccursposnegi f M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>f\<rbrakk> M e(i := S'))) \<and> (notdependalloccursposnegi f M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>f\<rbrakk> M e(i := S'))))"
  have "\<not> dependvari (nu f) M i \<longrightarrow> (mono (\<lambda>S'. \<lbrakk>nu f\<rbrakk> M e(i := S')) \<and> antimono (\<lambda>S'. \<lbrakk>nu f\<rbrakk> M e(i := S')))" using notdependsmono by metis
  moreover have "notdependalloccursposnegi f M (Suc i) True \<Longrightarrow> mono (\<lambda>S'. \<lbrakk>nu f\<rbrakk> M e(i := S'))" by (auto simp: assum1 numumono)
  moreover have "notdependalloccursposnegi f M (Suc i) False \<Longrightarrow> antimono (\<lambda>S'. \<lbrakk>nu f\<rbrakk> M e(i := S'))" by (auto simp: assum1 numuantimono)
  ultimately show "(\<not> dependvari (nu f) M i \<or> notdependalloccursposnegi f M (Suc i) True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>nu f\<rbrakk> M e(i := S'))) \<and> (\<not> dependvari (nu f) M i \<or> notdependalloccursposnegi f M (Suc i) False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>nu f\<rbrakk> M e(i := S')))" by auto
  have "\<not> dependvari (mu f) M i \<longrightarrow> (mono (\<lambda>S'. \<lbrakk>mu f\<rbrakk> M e(i := S')) \<and> antimono (\<lambda>S'. \<lbrakk>mu f\<rbrakk> M e(i := S')))" using notdependsmono by metis
  moreover have "notdependalloccursposnegi f M (Suc i) True \<Longrightarrow> mono (\<lambda>S'. \<lbrakk>mu f\<rbrakk> M e(i := S'))" by (auto simp: assum1 numumono)
  moreover have "notdependalloccursposnegi f M (Suc i) False \<Longrightarrow> antimono (\<lambda>S'. \<lbrakk>mu f\<rbrakk> M e(i := S'))" by (auto simp: assum1 numuantimono)
  ultimately show "(\<not> dependvari (mu f) M i \<or> notdependalloccursposnegi f M (Suc i) True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>mu f\<rbrakk> M e(i := S'))) \<and> (\<not> dependvari (mu f) M i \<or> notdependalloccursposnegi f M (Suc i) False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>mu f\<rbrakk> M e(i := S')))" by auto
qed

lemma monotonicitynotdependcoro : 
  shows "notdependalloccursposnegi f M 0 True \<Longrightarrow> mono (transformer f M e)"
  and "notdependalloccursposnegi f M 0 False \<Longrightarrow> antimono (transformer f M e)"
  apply (simp_all add: transformerdef)
proof-
  have "\<forall>S''. notdependalloccursposnegi f M 0 True \<longrightarrow> mono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M ((newenvironment e S'')(0 := S'))))" using monotonicitynotdepend by metis
  thus "notdependalloccursposnegi f M 0 True \<Longrightarrow> mono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M (newenvironment e S')))" by auto
next
  have "\<forall>S''. notdependalloccursposnegi f M 0 False \<longrightarrow> antimono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M ((newenvironment e S'')(0 := S'))))" using monotonicitynotdepend by metis
  thus "notdependalloccursposnegi f M 0 False \<Longrightarrow> antimono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M (newenvironment e S')))" by auto
qed

section \<open>approximation of \<open>nu\<close> and \<open>mu\<close>\<close>

lemma gfp_eq_nu [simp] :
"gfp (transformer f M e) = \<lbrakk>nu f\<rbrakk> M e"
  by (simp add: gfp_def transformer_def)

lemma lfp_eq_mu [simp] :
"lfp (transformer f M e) = \<lbrakk>mu f\<rbrakk> M e"
  by (simp add: lfp_def transformer_def)

lemma monosubset :
  assumes "mono f"
  shows "(f S' \<subseteq> S' \<longrightarrow> (f^^(Suc i)) S' \<subseteq> (f^^i) S') \<and>
    (S' \<subseteq> f S' \<longrightarrow> (f^^ i) S' \<subseteq> (f^^(Suc i)) S')"
  apply (induct i)
  using assms apply (simp_all add: mono_def)
  done

lemma fpoweriplusn : 
  assumes "((f :: 'a \<Rightarrow> 'a)^^i) S' = (f^^(Suc i)) S'"
  shows "(f^^(i + n)) S' = (f^^(Suc i + n)) S'" 
  apply (induct n)
  using assms apply simp
proof-
  fix n
  assume "(f ^^ (i + n)) S' = (f ^^ (Suc i + n)) S'"
  hence "f ((f ^^ (i + n)) S') = f ((f ^^ Suc (i + n)) S')" by simp
  thus "(f ^^ (i + Suc n)) S' = (f ^^ (Suc i + Suc n)) S'" by simp
qed

lemma fixpointmono:
  assumes "mono (f :: ('a set \<Rightarrow> 'a set))"
  and "finite (UNIV :: 'a set)"
  and "S' \<subseteq> f S' \<or> f S' \<subseteq> S'"
  shows "\<exists>n \<le> card(UNIV :: 'a set). (f^^n) S' = (f^^(Suc n)) S'"
proof (rule ccontr)
  assume "\<not> (\<exists>n\<le>card(UNIV :: 'a set).((f ^^ n) S') = ((f ^^ Suc n) S'))"
  hence assum1 : "\<forall>n\<le>card(UNIV :: 'a set).((f ^^ n) S') \<noteq> ((f ^^ Suc n) S')" by auto
  {
    assume assum2 : "S' \<subseteq> f S'"
    have  "\<forall>n \<le> Suc (card(UNIV :: 'a set)). card ((f ^^ n) S') \<ge> n"
    proof
      fix n
      show "n \<le> Suc (card(UNIV :: 'a set)) \<longrightarrow> n \<le> card ((f ^^ n) S')"
        apply (induct n)
        apply simp
      proof
        fix n
        assume assum3: "n \<le> Suc (card (UNIV :: 'a set)) \<longrightarrow> n \<le> card ((f ^^ n) S')"
        assume assum4 : "Suc n \<le> Suc (card (UNIV :: 'a set))"
        hence "n \<le> (card (UNIV :: 'a set))" by simp
        hence "(f ^^ n) S' \<noteq> (f ^^ (Suc n)) S'" using assum1 by simp
        moreover have "(f ^^ n) S' \<subseteq> (f ^^ (Suc n)) S'" using assms(1) assum2 monosubset by blast 
        ultimately have "(f ^^ n) S' \<subset> (f ^^ (Suc n)) S'" using psubset_eq by simp
        moreover have "finite ((f ^^ Suc n) S')" using assms(2) rev_finite_subset by auto
        ultimately have "card ((f ^^ n) S') < card ((f ^^ Suc n) S')" using psubset_card_mono by metis
        thus "Suc n \<le> card ((f ^^ Suc n) S')" using assum3 assum4 by simp
      qed
    qed
    hence contradiction1 : "card ((f ^^ Suc (card(UNIV :: 'a set))) S') \<ge>  Suc (card(UNIV :: 'a set))" by auto
    have contradiction2: "card ((f ^^ Suc (card(UNIV :: 'a set))) S') \<le> card(UNIV :: 'a set)" using assms(2) card_mono by auto
    have False using contradiction1 contradiction2 by auto
  }
  moreover{
    assume assum2 : "f S' \<subseteq> S'"
    have  "\<forall>n \<le> Suc (card(UNIV :: 'a set)). card ((f ^^ n) S') < Suc(card(UNIV :: 'a set)) - n"
    proof
      fix n
      show "n \<le> Suc (card(UNIV :: 'a set)) \<longrightarrow> card ((f ^^ n) S') < Suc (card(UNIV :: 'a set)) - n"
        apply (induct n)
        apply (simp add : assms(2) card_mono less_Suc_eq_le)
      proof
        fix n
        assume assum3: "n \<le> Suc (card (UNIV :: 'a set)) \<longrightarrow> card ((f ^^ n) S') < Suc(card (UNIV :: 'a set)) - n"
        assume assum4 : "Suc n \<le> Suc (card (UNIV :: 'a set))"
        hence "n \<le> (card (UNIV :: 'a set))" by simp
        hence "(f ^^ n) S' \<noteq> (f ^^ (Suc n)) S'" using assum1 by simp
        moreover have "(f ^^ (Suc n)) S' \<subseteq> (f ^^ n) S'" using assms(1) assum2 monosubset by blast 
        ultimately have "(f ^^ (Suc n)) S' \<subset> (f ^^  n) S'" using psubset_eq by simp
        moreover have "finite ((f ^^ n) S')" using assms(2) rev_finite_subset by auto
        ultimately have "card ((f ^^ (Suc n)) S') < card ((f ^^ n) S')" using psubset_card_mono by metis
        thus "card ((f ^^ Suc n) S') < Suc(card (UNIV :: 'a set)) - (Suc n)" using assum3 assum4 by simp
      qed
    qed
    hence "card ((f ^^ Suc (card(UNIV :: 'a set))) UNIV) <  0" by auto
    hence False by auto
  }
  ultimately show False using assms(3) by auto
qed

lemma gfp_monofin [simp] :
  assumes "(finite (UNIV :: 'a set))"
  and "mono (f :: 'a set \<Rightarrow> 'a set)"
  shows "(f^^(card (UNIV :: 'a set))) UNIV = gfp f"
proof-
  have "\<exists>n \<le> card(UNIV :: 'a set). (f^^n) (UNIV) = (f^^(Suc n)) (UNIV)" using assms fixpointmono by blast
  from this obtain n where assum2: "n \<le> card (UNIV :: 'a set) \<and>  (f^^n) (UNIV) = (f^^(Suc n)) (UNIV)" by auto
  hence "(f ^^ (n + (card (UNIV :: 'a set) - n))) (UNIV) = (f ^^ (Suc n +  (card (UNIV :: 'a set) - n))) (UNIV)" using fpoweriplusn by metis
  hence "(f^^(card (UNIV :: 'a set)))(UNIV) = (f^^Suc(card (UNIV :: 'a set)))(UNIV)" using assum2 by auto
  thus ?thesis using gfp_Kleene_iter assms(2) by blast
qed

lemma lfp_monofin [simp] :
  assumes "(finite (UNIV :: 'a set))"
  and "mono (f :: 'a set \<Rightarrow> 'a set)"
  shows "(f^^(card (UNIV :: 'a set))) {} = lfp f"
proof-
  have "\<exists>n \<le> card(UNIV :: 'a set). (f^^n) {} = (f^^(Suc n)) {}" using assms fixpointmono by blast
  from this obtain n where assum2: "n \<le> card (UNIV :: 'a set) \<and>  (f^^n) {} = (f^^(Suc n)) {}" by auto
  hence "(f ^^ (n + (card (UNIV :: 'a set) - n))) {} = (f ^^ (Suc n +  (card (UNIV :: 'a set) - n))) {}" using fpoweriplusn by metis
  hence "(f^^(card (UNIV :: 'a set))){} = (f^^Suc(card (UNIV :: 'a set))){}" using assum2 by auto
  thus ?thesis using lfp_Kleene_iter assms(2) by blast
qed

lemma transformer_eq_nu :
  assumes "finite (UNIV :: 's set)"
  and "mono (transformer f (M :: ('a, 's) lts) e)"
  shows "\<lbrakk>nu f\<rbrakk> M e = ((transformer f M e)^^(card (UNIV :: 's set)))(UNIV)"
  using assms by auto 

lemma transformer_eq_mu :
  assumes "finite (UNIV :: 's set)"
  and "mono (transformer f (M :: ('a, 's) lts) e)"
  shows "\<lbrakk>mu f\<rbrakk> M e = ((transformer f M e)^^(card (UNIV :: 's set))){}"
  using assms by auto

end