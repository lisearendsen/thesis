(*
    Author: Lise Arendsen, TU/e
*)

section \<open>Defining paths, some functions and results\<close>

theory paths
imports syntaxsemantics
begin

lemma inductfiniteset : 
  assumes "finite A"
  and "P {}"
  and "\<And>a A'. (a \<in> A-A' \<and> P A') \<Longrightarrow> P (insert a A')" 
  shows "P A"
  apply (rule finite_induct_select; simp add: assms)
  using psubset_imp_ex_mem apply blast
  done

text \<open>We define finite paths as lists of transitions
and infinite paths as mappings from natural numbers to transitions.\<close>

type_synonym ('a, 's) finpath = "('s \<times> 'a \<times> 's) list"
type_synonym ('a, 's) infpath = "('s \<times> 'a \<times> 's) word"

text \<open>A transition can be splitted into its source, action, and target.\<close>

definition source :: "('a \<times> 'b \<times> 'c) \<Rightarrow> 'a" where
"source t = fst t"

definition action :: "('a \<times> 'b \<times> 'c) \<Rightarrow> 'b" where
"action t = fst (snd t)"

definition target :: "('a \<times> 'b \<times> 'c) \<Rightarrow> 'c" where
"target t = snd (snd t)"

lemma sourceactiontargetsimp [simp] :
  shows "source (s, a, s') = s"
  and "action (s, a, s') = a"
  and "target (s, a, s') = s'"
  by (simp_all add: source_def action_def target_def)

lemma splittransition [simp] : "(source t, action t, target t) = t"
  by (simp add: source_def action_def target_def)

text \<open>Then we define the notion of valid paths, a finite path is valid with respect to its first 
state and last state, while an infinite path is valid only with respect to its first state.\<close>

fun validfinpath :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> ('a, 's) finpath \<Rightarrow> 's \<Rightarrow> bool" where
"validfinpath M s [] s' = (s = s')" |
"validfinpath M s (t#ts) s' = (s = source t \<and> t \<in> transition M \<and> validfinpath M (target t) ts s')"

definition validinfpath :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> ('a, 's) infpath \<Rightarrow> bool" where
"validinfpath M s p = (s = source (p 0) \<and> (\<forall>n. p n \<in> transition M \<and> (target (p n) = source (p (Suc n)))))"

text \<open>A path is either a finite path or an infinite path.\<close>

datatype ('a, 's) path = fin "('a, 's) finpath" | inf "('a, 's) infpath"

fun validpath :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> ('a, 's) path \<Rightarrow> bool" where
"validpath M s (fin p) = (\<exists>s'. validfinpath M s p s')" |
"validpath M s (inf p) = validinfpath M s p"

text \<open>Define \<open>enabled\<close> and \<open>locked\<close>.\<close>

definition enabledactionsset :: "('a, 's) lts \<Rightarrow> 's set \<Rightarrow> 'a set" where
"enabledactionsset M S' = {a . (\<forall>s \<in> S'. \<exists>s'. (s, a, s') \<in> transition M)}"

abbreviation enabledactions :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> 'a set" where
"enabledactions M s \<equiv> enabledactionsset M {s}"

lemma enabledactions_def [simp] : "enabledactions M s = {a . (\<exists>s'. (s, a, s') \<in> transition M)}"
  by (simp add: enabledactionsset_def)

definition enabled :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> 'a set \<Rightarrow> bool" where
"enabled M s \<alpha> \<equiv> (\<exists> a \<in> \<alpha>. a \<in> enabledactions M s)"

lemma actionenabled : "enabledactions M s \<noteq> {} = (\<exists>a s'. (s, a, s') \<in> transition M)"
  by simp

definition locked :: "('a, 's) lts \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> bool" where
"locked M B s = (enabledactions M s \<subseteq> B)"

lemma lockednegenabled : "locked M B s = (\<not> enabled M s (-B))" 
  by (auto simp: locked_def enabled_def)

text \<open>A finite path matches a regular formula if and only if its sequence of actions is in the language 
of the regular formula.\<close>

definition match :: "'a rexp \<Rightarrow> ('a, 's) finpath \<Rightarrow> bool" where
"match \<rho> p = (map action p \<in> lang \<rho>)"

text \<open>A finite path matches a regular formula n times if and only if its sequence of actions is in the 
language of the regular formula concatenated n times.\<close>

fun matchntimes :: "nat \<Rightarrow> 'a rexp \<Rightarrow> ('a, 's) finpath \<Rightarrow> bool" where
"matchntimes 0 R p = (p = [])" |
"matchntimes (Suc n) R p = (\<exists>p' p''. p = p' @ p'' \<and> match R p' \<and> matchntimes n R p'')"

text \<open>A finite path \<open>p\<close> matches \<open>Star R\<close> (Kleene star) if and only if there exists \<open>n\<close> such that 
\<open>p\<close> matches \<open>R\<close> \<open>n\<close> times. Makes reasoning about matching \<open>Star R\<close> easier\<close>

lemma matchstar_eq_matchntimes : "match (R\<^sup>\<star>) p = (\<exists>n. matchntimes n R p)"
proof-
  have "match (Star R) p = (map action p \<in> (\<Union>n. (lang R) ^^ n))" by (simp add: match_def star_def)
  moreover have "... = (\<exists>n. map action p \<in> (lang R) ^^ n)" by auto
  moreover have "\<forall>n. (map action p \<in> (lang R) ^^ n) = (matchntimes n R p)"
  proof
    fix n
    show "(map action p \<in> (lang R) ^^ n) = (matchntimes n R p)"
    apply (induct n arbitrary : p; simp)
    proof-
      fix n
      fix p :: "('a, 's) finpath"
      assume assum1 : "(\<And>(p :: ('a, 's) finpath). (map action p \<in> lang R ^^ n) = matchntimes n R p)"
      have "(map action p \<in> lang R @@ lang R ^^ n) = (\<exists>p' p''. p = p' @ p'' \<and>  ((map action p') \<in> lang R) \<and> ((map action p'') \<in> lang R ^^ n))" by (rule exists_map_abinconc)
      moreover have "... = (\<exists>p' p''. p = p'@p'' \<and>  match R p' \<and>  matchntimes n R p'')" using assum1 by (auto simp: match_def) 
      ultimately show "(map action p \<in> lang R @@ lang R ^^ n) = (\<exists>p' p''. p = p' @ p'' \<and> match R p' \<and> matchntimes n R p'')" by simp
    qed
  qed
  ultimately show ?thesis by blast
qed

text \<open>Simplifications of match for all patterns of regular formulas.\<close>

lemma matchunfold [simp] : 
  shows "match Zero p = False"
  and "match One p = (p = [])"
  and "match ({a}\<^sub>R) p = (\<exists>t. p = [t] \<and> action t = a)"
  and "match (R +\<^sub>R Q) p = (match R p \<or> match Q p)"
  and "match (R \<cdot> Q) p = (\<exists>p' p''. p = p' @ p'' \<and> match R p' \<and> match Q p'')"
  apply (simp_all add: match_def exists_map_abinconc)
  apply (rule iffI; auto)
  done

lemma matchunfoldActslist [simp] : "match (Actslist A) p = (\<exists>t. p = [t] \<and> action t \<in> set A)"
  by (induct A; auto)

lemma matchunfoldActs [simp] : "finite A \<Longrightarrow> match (Acts A) p = (\<exists>t. p = [t] \<and> action t \<in> A)"
  by (simp add: Acts_def; rule someI2_ex; simp add: finite_list)

text \<open>Defining notions of occurrence.
A set of actions \<open>A\<close> occurs on path \<open>p\<close> if and only if there exists an action in A 
that occurs along the path.\<close>

fun alloccurringmap :: "(('s \<times> 'a \<times> 's) \<Rightarrow> 'b) \<Rightarrow> ('a, 's) path \<Rightarrow> 'b set" where
"alloccurringmap f (fin p) = set (map f p)" |
"alloccurringmap f (inf p) = image f (range p)"

abbreviation alloccurringstates :: "'s \<Rightarrow> ('a, 's) path \<Rightarrow> 's set" where
"alloccurringstates s p \<equiv> insert s (alloccurringmap target p)"

abbreviation alloccurringactions :: "('a, 's) path \<Rightarrow> 'a set" where
"alloccurringactions p \<equiv> alloccurringmap action p"

definition occurs :: "'a set \<Rightarrow> ('a, 's) path \<Rightarrow> bool" where
"occurs A p \<equiv> (\<exists> a \<in> A. a \<in> alloccurringactions p)"

lemma occurssimps [simp] : 
  shows "occurs A (fin p) = (\<exists> a \<in> A. a \<in> set (map action p))"
  and "occurs A (inf p') = (\<exists> a \<in> A. a \<in> image action (range p'))"
  by (simp_all add: occurs_def)

lemma alloccursnotoccurs : "alloccurringactions p \<subseteq> A = (\<not>occurs (-A) p)"
  unfolding occurs_def by auto

lemma occurs_map_exists_fin : "a \<in> set (map f p) = (\<exists>n < length p. f (p!n) = a)"
  apply (simp add: image_iff)
  using in_set_conv_nth apply metis
  done

text \<open>A finite path matches \<open>Star (Acts A)\<close> (A Kleene star) if and only if 
  all its actions are in \<open>A\<close>.\<close>

lemma matchstaract : "finite A \<Longrightarrow> match (Acts A\<^sup>\<star>) p = (alloccurringactions (fin p) \<subseteq> A)"
  apply (induct p; simp add: matchstar_eq_matchntimes)
  apply (subgoal_tac "matchntimes 0 (Acts A) []")
  apply blast
  apply (simp)
proof
  fix t 
  fix p :: "('a, 's) finpath"
  assume assum1: "(\<exists>n. matchntimes n (Acts A) p) = (action ` set p \<subseteq> A)"
  assume assum2 : "finite A"
  assume "\<exists>n. matchntimes n (Acts A) (t # p)"
  then obtain n where "matchntimes n (Acts A) (t # p)" by auto
  thus "action t \<in> A \<and> action ` set p \<subseteq> A" 
    apply (induct n)
    using assum1 assum2 apply auto
    done
next
  fix t :: "'s \<times> 'a \<times> 's" 
  fix p :: "('a, 's) finpath"
  assume "(\<exists>n. matchntimes n (Acts A) p) = (action ` set p \<subseteq> A)"
  then obtain n where assum1: "matchntimes n (Acts A) p = (action ` set p \<subseteq> A)" by auto
  assume assum2: "finite A"
  assume "action t \<in> A \<and> action ` set p \<subseteq> A"
  hence "t # p = [t] @ p \<and> action t \<in> A \<and> matchntimes n (Acts A) p" using assum1 by simp
  hence "matchntimes (Suc n) (Acts A) (t # p)" unfolding matchntimes.simps using matchunfoldActs assum2 by blast
  thus "\<exists>n. matchntimes n (Acts A) (t # p)" by blast
qed

text \<open>Defining operations on paths and some simplifications for these operations.\<close>

fun pref :: "nat \<Rightarrow> ('a, 's) path \<Rightarrow> ('a, 's) finpath" where 
"pref i (fin p) = take i p" |
"pref i (inf p) = prefix i p"

fun suff :: "nat \<Rightarrow> ('a, 's) path \<Rightarrow> ('a, 's) path" where 
"suff i (fin p) = fin (drop i p)" |
"suff i (inf p) = inf (suffix i p)"

fun ind :: "nat \<Rightarrow> ('a, 's) path \<Rightarrow> ('s \<times> 'a \<times> 's)" where
"ind i (fin p) = p!i" |
"ind i (inf p) = p i"

lemma emptylist [simp] : "(pref i p = []) = (i = 0 \<or> p = fin [])"
  using take_eq_Nil by (cases p) simp_all

lemma nosuffix [simp] : "(p = fin [] \<or> i = 0) \<Longrightarrow> (suff i p = p)"
  by (cases p; auto)

fun indicespath :: "('a, 's) path \<Rightarrow> nat set" where
"indicespath (fin p) = ({n. n < length p})" |
"indicespath (inf p) = UNIV"

fun laststate :: "'s \<Rightarrow> ('a, 's) finpath \<Rightarrow> 's" where
"laststate s [] = s" |
"laststate s p = target (last p)"

lemma laststatesimps:
  shows "p = [] \<Longrightarrow> laststate s (t # p) = target t "
  and "p \<noteq> [] \<Longrightarrow> laststate s (t # p) = laststate s' p"
  apply simp
  apply (induct p; simp)
  done

lemma laststate_conc [simp]: "laststate s (p @ p') = laststate (laststate s p) p'" 
  by (induct p; induct p'; simp add: laststatesimps)

lemma laststatetarget [simp]:
  shows "laststate s (t # p) = laststate (target t) p"
  by (cases p; simp)

lemma validfinpathlaststate : "validfinpath M s p s' \<Longrightarrow> laststate s p = s'"
  by (induct p arbitrary: s, simp, simp del: laststate.simps)

lemma validfinpathuniquelaststate : "validfinpath M s p s' \<and> validfinpath M s p s'' \<Longrightarrow> s' = s''"
  by (induct p arbitrary : s; auto)

lemma prefleft : "n \<in> indicespath p \<Longrightarrow> (pref (Suc n) p) = (ind 0 p) # (pref n (suff (Suc 0) p))"
  by (cases p; induct n; simp add: take_Suc_conv_app_nth)

text \<open>Simplifications for valid paths, in particular on extensions and subpaths.\<close>

lemma validfinpathsplit [simp] : "validfinpath M s (p @ p') s' = (\<exists>s''. validfinpath M s p s'' \<and> validfinpath M s'' p' s')"
  by (induct p arbitrary: s; simp)

lemma shiftinfvalidpath [simp]: "validinfpath M s (t ## p) = (s = source t \<and> t \<in> transition M \<and> validinfpath M (target t) p)"
proof-
  have "(\<forall>n. (n = 0 \<longrightarrow> t \<in> transition M \<and> target t = source (p 0)) \<and> (0 < n \<longrightarrow> p (n - Suc 0) \<in> transition M \<and> target (p (n - Suc 0)) = source (p n))) =
    (t \<in> transition M \<and> target t = source (p 0) \<and> (\<forall>n. (0 < n \<longrightarrow> p (n - Suc 0) \<in> transition M \<and> target (p (n - Suc 0)) = source (p n))))" by auto
  moreover have "... = (t \<in> transition M \<and> target t =  source (p 0) \<and> (\<forall>n. p n \<in> transition M \<and> target (p n) = source (p (Suc n))))" by auto
  ultimately have "(validinfpath M s (conc [t] p)) = (s = source t \<and> t \<in> transition M \<and> validinfpath M (target t) p)" by (simp add: validinfpath_def conc_def)
  thus ?thesis by simp
qed

lemma validinfpathsplit [simp] : "validinfpath M s (conc p p') = (\<exists>s'. validfinpath M s p s' \<and> validinfpath M s' p')"
  by (induct p arbitrary: s; simp)

lemma validinfpathsplitlaststate : "(validfinpath M s p (laststate s p) \<and> validinfpath M (laststate s p) p') = validinfpath M s (conc p p')"
  using validinfpathsplit validfinpathlaststate by metis

lemma validfinsubpath [simp] : "i < length p \<and> validfinpath M s p s' \<Longrightarrow> validfinpath M s (take i p) (source (p!i))"
  apply (induct p arbitrary: s i, simp)
proof-
  case Cons
  then show ?case by (cases i; auto)
qed

lemma validfinpathtakelaststate : "n < length p \<and> validfinpath M s p s' \<Longrightarrow> laststate s (take n p) = source (p!n)"
  using validfinpathlaststate validfinsubpath by meson

lemma validfinsubpathtarget [simp] : "i < length p \<and> validfinpath M s p s' \<Longrightarrow> validfinpath M s (take (Suc i) p) (target (p!i))"
  apply (induct p arbitrary: s i, simp)
proof-
  case Cons
  then show ?case by (cases i; auto)
qed

lemma validfinsubpathright [simp] : "i < length p \<and> validfinpath M s p s' \<Longrightarrow> validfinpath M (source (p!i)) (drop i p) s'"
  apply (induct p arbitrary: s i, simp)
proof-
  case Cons
  then show ?case by (cases i; auto)
qed

lemma validfinsubpathtargetright [simp] : "i < length p \<and> validfinpath M s p s' \<Longrightarrow> validfinpath M (target (p!i)) (drop (Suc i) p) s'"
  apply (induct p arbitrary: s i, simp)
proof-
  case Cons
  then show ?case by (cases i; auto)
qed
 
lemma validinfsubpath [simp] : "validinfpath M s p \<Longrightarrow> validfinpath M s (prefix i p) (source (p i))"
  by (induct i arbitrary : s p; simp add: validinfpath_def)

lemma validinfpathprefixlaststate : "validinfpath M s p \<Longrightarrow> laststate s (prefix n p) = source (p n)"
  using validfinpathlaststate validinfsubpath by meson

lemma validinfsubpathright [simp] : "validinfpath M s p \<Longrightarrow> validinfpath M (source (p i)) (suffix i p)"
  by (induct i; simp add: validinfpath_def)

lemma validinfsubpathtargetright [simp] : "validinfpath M s p \<Longrightarrow> validinfpath M (target (p i)) (suffix (Suc i) p)"
  by (induct i; simp add: validinfpath_def)

lemma zerothtransitionfinpath : "0 < length p \<and> validfinpath M s p s' \<Longrightarrow> (p!0 \<in> transition M)"
  by (induct p; simp)

text \<open>The \<open>i\<close>'th transition in a valid path is in the transitions of the labeled transition system\<close>

lemma ithtransitionfinpath [simp] : "i < length p \<and> validfinpath M s p s' \<Longrightarrow> p!i \<in> transition M"
proof-
  assume assum1: "i < length p \<and> validfinpath M s p s'"
  hence "0 < length (drop i p) \<and> validfinpath M (source (p!i)) (drop i p) s'" by auto
  hence "(drop i p)!0 \<in> transition M" by (rule zerothtransitionfinpath)
  moreover have "(drop i p)!0 = p!i" using assum1 by auto
  ultimately show ?thesis by simp
qed

lemma validfinpathsource : "p \<noteq> [] \<and> validfinpath M s p s' \<longrightarrow> s = source (p!0)"
  by (induct p arbitrary : s; simp)

lemma zerothtargetsourcefinpath : "Suc 0 < length p \<and> validfinpath M s p s' \<Longrightarrow> target (p!0) = source (p!(Suc 0))"
  by (induct p; auto simp : validfinpathsource)

lemma ithtargetsourcefinpath [simp] : "Suc i < length p \<and> validfinpath M s p s' \<Longrightarrow> target (p!i) = source (p!(Suc i))"
proof-
  assume assum1: "Suc i < length p \<and> validfinpath M s p s'"
  hence "Suc 0 < length (drop i p) \<and> validfinpath M (source (p!i)) (drop i p) s'" by auto
  hence "target ((drop i p)!0) = source ((drop i p)!(Suc 0))" by (rule zerothtargetsourcefinpath)
  moreover have "(drop i p)!0 = p!i \<and> (drop i p)!(Suc 0) = p!(Suc i)" using assum1 by auto
  ultimately show ?thesis by simp
qed

text \<open>Some recurring formulas and simplifications.\<close>

lemma Boxcomplement_locked : "finite (-B) \<Longrightarrow> s \<in> \<lbrakk>[Acts (-B)]\<^sub>R ff\<rbrakk> M e = locked M B s"
  by (simp add: locked_def del: Box.simps; auto)

lemma Diamond_enabled : "finite (\<alpha>\<^sub>e) \<Longrightarrow> s \<in> \<lbrakk>\<langle>Acts \<alpha>\<^sub>e\<rangle>\<^sub>R tt\<rbrakk> M e = enabled M s \<alpha>\<^sub>e"
  by (simp del: Diamond.simps; auto simp: enabled_def)

lemma finitesubsetUNIV [simp] : "finite (UNIV :: 'a set) \<Longrightarrow> finite (A :: 'a set)"
  using finite_subset subset_UNIV by blast

lemma validfinpathmatchacts [simp] : "finite A \<Longrightarrow> (validfinpath M s p s' \<and> match (Acts A) p) = (\<exists>a \<in> A. (s, a, s') \<in> transition M \<and> p = [(s, a, s')])"
  by auto

lemma Diamondactsempty [simp] : "finite A \<Longrightarrow> \<lbrakk>f\<rbrakk> M e = {} \<Longrightarrow> \<lbrakk>\<langle>Acts A\<rangle>\<^sub>R f\<rbrakk> M e = {}"
  by simp

lemma Diamondempty [simp] : "\<lbrakk>f\<rbrakk> M e = {} \<Longrightarrow> \<lbrakk>\<langle>R\<rangle>\<^sub>R f\<rbrakk> M e = {}"
  by (induct R arbitrary : f e; auto)

lemma Diamondmatch :
  "s \<in> \<lbrakk>\<langle>R\<rangle>\<^sub>R f\<rbrakk> M e = (\<exists>p s'. validfinpath M s p s' \<and> match R p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e)"
  apply (induct R arbitrary : f s e)
  apply simp+
  apply force
  apply simp
  apply blast
  apply simp
proof-
  fix R Q f s e
  have "(\<exists>p s'. validfinpath M s p s' \<and> match R p \<and> (\<exists>p s''. validfinpath M s' p s'' \<and> match Q p \<and> s'' \<in> \<lbrakk>f\<rbrakk> M e)) = (\<exists>p p' s''. (\<exists>s'. validfinpath M s p s' \<and> validfinpath M s' p' s'') \<and> match R p \<and> match Q p' \<and> s'' \<in> \<lbrakk>f\<rbrakk> M e)" by blast
  moreover have "... = (\<exists>p p' s''. validfinpath M s (p @ p') s'' \<and> match R p \<and> match Q p' \<and> s'' \<in> \<lbrakk>f\<rbrakk> M e)" by simp
  ultimately show "(\<exists>p s'. validfinpath M s p s' \<and> match R p \<and> (\<exists>p s''. validfinpath M s' p s'' \<and> match Q p \<and> s'' \<in> \<lbrakk>f\<rbrakk> M e)) = (\<exists>p s'. validfinpath M s p s' \<and> (\<exists>p' p''. p = p' @ p'' \<and> match R p' \<and> match Q p'') \<and> s' \<in> \<lbrakk>f\<rbrakk> M e)" by blast
next
  fix f s e
  case IH: (Star R)
  show ?case
    apply (rule iffI)
  proof-
    let ?S' = "{s. \<exists>p s'. validfinpath M s p s' \<and> match (Star R) p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e}"
    have "\<And>s. s \<in> \<lbrakk>f\<rbrakk> M e \<Longrightarrow> validfinpath M s [] s \<and> match (Star R) [] \<and> s \<in> \<lbrakk>f\<rbrakk> M e" unfolding match_def by auto
    hence "\<lbrakk>f\<rbrakk> M e \<subseteq> ?S'" by blast
    moreover {
      fix s 
      assume "s \<in> \<lbrakk>Diamond R (var 0)\<rbrakk> M (newenvironment e ?S')"
      from this IH obtain p s' p' s'' where "validfinpath M s p s' \<and> match R p \<and> validfinpath M s' p' s'' \<and> match (Star R) p' \<and> s'' \<in> \<lbrakk>f\<rbrakk> M e" by auto
      hence "validfinpath M s (p @ p') s'' \<and> match (Star R) (p @ p') \<and> s'' \<in> \<lbrakk>f\<rbrakk> M e" unfolding match_def by auto
      hence "s \<in> ?S'" by blast
    }
    ultimately have "\<lbrakk>Diamond R (var 0)\<rbrakk> M (newenvironment e ?S') \<union> \<lbrakk>f\<rbrakk> M e \<subseteq> ?S'" by blast
    moreover assume "s \<in> \<lbrakk>Diamond (Star R) f\<rbrakk> M e"
    ultimately show "\<exists>p s'. validfinpath M s p s' \<and> match (Star R) p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e" by auto
  next
    assume "\<exists>p s'. validfinpath M s p s' \<and> match (Star R) p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e"
    then obtain p s' n where assum1: "validfinpath M s p s' \<and>  matchntimes n R p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e" by (auto simp: matchstar_eq_matchntimes)
    show "s \<in> \<lbrakk>Diamond (Star R) f\<rbrakk> M e"
      apply simp
      apply (rule allI impI)+
    proof-
      fix S'
      assume assum2 : "\<lbrakk>Diamond R (var 0)\<rbrakk> M (newenvironment e S') \<subseteq> S' \<and> \<lbrakk>f\<rbrakk> M e \<subseteq> S'"
      have "(s' \<in> \<lbrakk>f\<rbrakk> M e \<and> matchntimes n R p \<and> validfinpath M s p s') \<Longrightarrow> s \<in> S'"
        apply (induct n arbitrary: s p; simp)
        using assum1 assum2 apply blast
      proof-
        fix n s p
        assume assum3 : "(\<And>s p. matchntimes n R p \<and> validfinpath M s p s' \<Longrightarrow> s \<in> S')"
        assume "s' \<in> \<lbrakk>f\<rbrakk> M e \<and> (\<exists>p' p''. p = p' @ p'' \<and> match R p' \<and> matchntimes n R p'') \<and> validfinpath M s p s'"
        then obtain p' p'' s'' where "s' \<in> \<lbrakk>f\<rbrakk> M e \<and>  match R p' \<and> matchntimes n R p'' \<and> validfinpath M s p' s'' \<and> validfinpath M s'' p'' s'"  using validfinpathsplit by metis
        hence "s \<in> \<lbrakk>Diamond R (var 0)\<rbrakk> M (newenvironment e S')" using assum3 IH by auto
        thus "s \<in> S'" using assum2 by auto
      qed
      thus "s \<in> S'" using assum1 by auto
    qed
  qed
qed

text \<open>For small examples (for which the formula holds in all states) 
  we do not have to use \<open>Diamondmatch\<close>; auto will solve the lemma.
  The absence of such paths is harder to prove.\<close>

lemma example_Star: "\<lbrakk>\<langle>{\<b>}\<^sub>R\<^sup>\<star> \<cdot> {\<a>}\<^sub>R\<rangle>\<^sub>R tt\<rbrakk> example_lts e = {s\<^sub>0, s\<^sub>1, s\<^sub>2}"
  apply (rule subset_antisym)
  using example_states.exhaust apply blast
  apply (auto simp: example_lts_def)
  done

lemma Diamondor : "\<lbrakk>\<langle>R\<rangle>\<^sub>R (f \<or>\<^sub>\<mu> g)\<rbrakk> M e = \<lbrakk>\<langle>R\<rangle>\<^sub>R f \<or>\<^sub>\<mu> \<langle>R\<rangle>\<^sub>R g\<rbrakk> M e"
proof-
  have "\<And>s. s \<in> \<lbrakk>Diamond R (or f g)\<rbrakk> M e = (s \<in> \<lbrakk>or (Diamond R f) (Diamond R g)\<rbrakk> M e)" by (auto simp: Diamondmatch)
  thus ?thesis by auto
qed

lemma Boxmatch : "s \<in> \<lbrakk>[R]\<^sub>R f\<rbrakk> M e = (\<forall>p s'. validfinpath M s p s' \<and> match R p \<longrightarrow> s' \<in> \<lbrakk>f\<rbrakk> M e)"
proof-
  have "\<lbrakk>Box R f\<rbrakk> M e = \<lbrakk>neg (Diamond R (neg f))\<rbrakk> M e" by (subst negDiamond; rule Box_eq; simp)
  moreover have "s \<in> \<lbrakk>Diamond R (neg f)\<rbrakk> M e = (\<exists>p s'. validfinpath M s p s' \<and> match R p \<and> s' \<notin> \<lbrakk>f\<rbrakk> M e)" by (subst Diamondmatch; simp)
  ultimately show ?thesis by auto
qed 

lemma Boxand : "\<lbrakk>[R]\<^sub>R (f \<and>\<^sub>\<mu> g)\<rbrakk> M e = \<lbrakk>[R]\<^sub>R f \<and>\<^sub>\<mu> [R]\<^sub>R g\<rbrakk> M e"
proof-
  have "\<And>s. s \<in> \<lbrakk>Box R (and' f g)\<rbrakk> M e = (s \<in> \<lbrakk>and' (Box R f) (Box R g)\<rbrakk> M e)" by (auto simp: Boxmatch)
  thus ?thesis by auto
qed

text \<open>Simplification rules for occurrence.\<close>

lemma addpathsnotoccurs: "validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> validfinpath M s' p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<Longrightarrow> validfinpath M s (p @ p') s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin (p @ p'))"
  by auto

lemma alloccurringactionsfin : "alloccurringactions (fin p) = {action (p!n)| n. n < length p}"
proof-
  have "alloccurringactions (fin p) = {a. a \<in> set (map action p)}" by simp
  moreover have "... = {a. \<exists>n < length p. action (p!n) = a}" by (subst occurs_map_exists_fin; simp)
  ultimately show "alloccurringactions (fin p) = {action (p!n)| n. n < length p}" by auto
qed

lemma alloccurringactionsfinright : "alloccurringactions (fin (drop i p)) \<subseteq> alloccurringactions (fin p)" 
  unfolding alloccurringactionsfin by auto

lemma alloccurringactionsfinleft : "alloccurringactions (fin (take i p)) \<subseteq> alloccurringactions (fin p)" 
  unfolding alloccurringactionsfin by auto

lemma occurs_max_exists : "a \<in> set (map action p) \<Longrightarrow> (\<exists>n < length p. action (p!n) = a \<and> a \<notin> alloccurringactions (fin (drop (Suc n) p)))"
proof-
  let ?n = "Max {n. n < length p \<and> action (p!n) = a}"
  assume "a \<in> set (map action p)"
  hence "\<exists>n < length p. action (p!n) = a" using occurs_map_exists_fin by metis
  hence max_exists: "finite {n. n < length p \<and> action (p!n) = a} \<and> {n. n < length p \<and> action (p!n) = a} \<noteq> {}" by auto 
  hence "\<forall>m. m < length p \<and> m > ?n \<longrightarrow> action (p!m) \<noteq> a" using Max_ge leD by blast
  moreover have "\<And>n. (\<forall>m. m < length p \<and> m > n \<longrightarrow> action (p!m) \<noteq> a) \<Longrightarrow> (\<forall>m < length (drop (Suc n) p). action ((drop (Suc n) p)!m) \<noteq> a)" by auto
  ultimately have "\<forall>m < length (drop (Suc ?n) p). action ((drop (Suc ?n) p)!m) \<noteq> a" by blast
  hence "a \<notin> alloccurringactions (fin (drop (Suc ?n) p))" unfolding alloccurringactionsfin by auto
  moreover have "?n < length p \<and> action (p!?n) = a" using max_exists Max_in by blast
  ultimately show "\<exists>n < length p. action (p!n) = a \<and> a \<notin> alloccurringactions (fin (drop (Suc n) p))" by auto
qed

lemma occursfinalternative : "occurs A (fin p) = (\<exists>n < length p. action (p!n) \<in> A)"
  unfolding occurssimps alloccurringmap.simps using occurs_map_exists_fin by metis

lemma occursinfalternative : "occurs A (inf p) = (\<exists> n. action (p n) \<in> A)"
  by auto

lemma notoccursempty: "\<not>occurs {} (fin p)" 
  by (simp add: occurs_def)

lemma alloccurringstatesalternative : "alloccurringstates s p = insert s {target (ind i p) | i. i \<in> indicespath p}"
  apply (cases p; auto)
  using in_set_conv_nth sourceactiontargetsimp(3) apply metis
  done

lemma alloccurringstatesinset : "s \<in> S' \<and> (\<forall>n \<in> indicespath p. target (ind n p) \<in> S') \<Longrightarrow> alloccurringstates s p \<subseteq> S'"
  unfolding alloccurringstatesalternative by auto

lemma sourcetargetfin : "validfinpath M s p s' \<Longrightarrow> insert s (set (map target p)) = insert s' (set (map source p))"
  by (induct p arbitrary: s; auto) 

lemma laststateoccurs: "validfinpath M s p s' \<Longrightarrow> s' \<in> alloccurringstates s (fin p)"
  unfolding alloccurringmap.simps by (subst sourcetargetfin; auto)

definition occursstate :: "'s set \<Rightarrow> 's \<Rightarrow> ('a, 's) path \<Rightarrow> bool" where
"occursstate S' s p \<equiv> (\<exists>s' \<in> S'. s' \<in> alloccurringstates s p)"

lemma occursstatesimps [simp] : 
  shows "occursstate S' s (fin p) = (\<exists> s' \<in> S'. s' \<in> insert s (set (map target p)))" 
  and "occursstate S' s (inf p') = (\<exists> s' \<in> S'. s' \<in> insert s (image target (range p')))"
  by (simp_all add: occursstate_def)

lemma occursstatealternative : "occursstate S' s p = (s \<in> S' \<or> (\<exists> n \<in> indicespath p. target (ind n p) \<in> S'))"
  apply (cases p; simp add: image_iff)
  using in_set_conv_nth apply metis
  apply auto
  done

lemma notemptypath : "s \<notin> S' \<and> (occursstate S' s (fin p) \<or> occurs A (fin p)) \<longrightarrow> p \<noteq> []" 
  by (cases p; simp)

lemma notoccursendpath : "validfinpath M s p s' \<and> \<not>occursstate S' s (fin p) \<Longrightarrow> s' \<notin> S'"
proof-
  assume "validfinpath M s p s' \<and> \<not>occursstate S' s (fin p)"
  hence "validfinpath M s p s' \<and> \<not>(\<exists>s'\<in>S'. s' \<in> insert s (set (map target p)))" by simp
  hence "\<forall> s'' \<in> S'. s'' \<notin> insert s' (set (map source p))" using sourcetargetfin by metis
  thus ?thesis by auto
qed

text \<open>Defining completeness criteria.\<close>

fun progressing :: "('a, 's) lts \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> ('a, 's) path \<Rightarrow> bool" where
"progressing M B s (fin p) = locked M B (laststate s p)" |
"progressing M B s (inf p) = True"

definition perpetuallyenabled :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> ('a, 's) path \<Rightarrow> 'a set" where
"perpetuallyenabled M s p = {a . (\<forall>s \<in> alloccurringstates s p. a \<in> enabledactions M s)}"

lemma perpetuallyenabled_alternative: "perpetuallyenabled M s p = enabledactionsset M (alloccurringstates s p)"
  by (simp add: enabledactionsset_def perpetuallyenabled_def)

definition allsuffixes :: "'s \<Rightarrow> ('a, 's) path \<Rightarrow> ('s \<Rightarrow> ('a, 's) path \<Rightarrow> bool) \<Rightarrow> bool" where
"allsuffixes s p P = (P s p \<and> (\<forall>i \<in> indicespath p. P (target (ind i p)) (suff (Suc i) p)))"

definition relentlesslyenabled :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> ('a, 's) path \<Rightarrow> 'a set" where
"relentlesslyenabled M s p = {a . allsuffixes s p (\<lambda>s p. \<exists>s \<in> alloccurringstates s p. a \<in> enabledactions M s)}"

definition reachableactionsset :: "('a, 's) lts \<Rightarrow> 'a set \<Rightarrow> 's set \<Rightarrow> 'a set" where
"reachableactionsset M B S' = {a. \<forall>s \<in> S'. \<exists>p s'. validfinpath M s p s' \<and> \<not>occurs B (fin p) \<and> a \<in> enabledactions M s'}"

lemma reachableactionsstatessubset : "A' \<subseteq> A \<Longrightarrow> reachableactionsset M B A \<subseteq> reachableactionsset M B A'"
  by (auto simp: reachableactionsset_def)

lemma reachableactionssubset : "B' \<subseteq> B \<Longrightarrow> reachableactionsset M B S' \<subseteq> reachableactionsset M B' S'"
  unfolding reachableactionsset_def occurs_def by blast

definition reachableactions :: "('a, 's) lts \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> 'a set" where
"reachableactions M B s = reachableactionsset M B {s}"

lemma reachableactionsdef : "reachableactions M B s = {a. \<exists>p s'. validfinpath M s p s' \<and> \<not>occurs B (fin p) \<and> a \<in> enabledactions M s'}"
  by (simp add: reachableactions_def reachableactionsset_def)

lemma enabled_reachable : "enabledactions M s \<subseteq> reachableactions M B s"
  unfolding enabledactions_def reachableactions_def reachableactionsset_def
  by (subgoal_tac "validfinpath M s [] s \<and> \<not>occurs B (fin [])"; (blast|simp))

lemma Diamondreachable : "finite (-B) \<Longrightarrow> s \<in> \<lbrakk>\<langle>Acts (-B)\<^sup>\<star>\<rangle>\<^sub>R \<langle>a\<rangle>\<^sub>\<mu>tt\<rbrakk> M e = (a \<in> reachableactions M B s)"
  by (simp only: Diamondmatch matchstaract reachableactionsdef, auto)

lemma Boxnotreachable : "finite (-B) \<Longrightarrow> s \<in> \<lbrakk>[Acts (-B)\<^sup>\<star>]\<^sub>R [a]\<^sub>\<mu>ff\<rbrakk> M e = (a \<notin> reachableactions M B s)"
  by (simp only: Boxmatch matchstaract reachableactionsdef, auto)

definition perpetuallyreachable :: "('a, 's) lts \<Rightarrow> 'a set \<Rightarrow>'s \<Rightarrow> ('a, 's) path \<Rightarrow> 'a set" where
"perpetuallyreachable M B s p = {a . (\<forall>s \<in> alloccurringstates s p. a \<in> reachableactions M B s)}"

lemma perpetuallyenabled_perpetuallyreachable : "perpetuallyenabled M s p \<subseteq> perpetuallyreachable M B s p"
  unfolding perpetuallyenabled_def perpetuallyreachable_def using enabled_reachable by fastforce

lemma perpetuallyenabled_relentlesslyenabled : "perpetuallyenabled M s p \<subseteq> relentlesslyenabled M s p"
  by (auto simp: relentlesslyenabled_def perpetuallyenabled_alternative enabledactionsset_def allsuffixes_def alloccurringstatesalternative)

definition relentlesslyreachable :: "('a, 's) lts \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> ('a, 's) path \<Rightarrow> 'a set" where
"relentlesslyreachable M B s p = {a . allsuffixes s p (\<lambda>s p. \<exists>s \<in> alloccurringstates s p. a \<in> reachableactions M B s)}"

lemma relentlesslyenabled_relentlesslyreachable: "relentlesslyenabled M s p \<subseteq> relentlesslyreachable M B s p"
  unfolding relentlesslyenabled_def relentlesslyreachable_def allsuffixes_def using enabled_reachable by fastforce

definition WFA :: "('a, 's) lts \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> ('a, 's) path \<Rightarrow> bool" where
"WFA M B s p = allsuffixes s p (\<lambda>s p. perpetuallyenabled M s p -B \<subseteq> alloccurringactions p)"

abbreviation preimagerelation :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set" where 
"preimagerelation A A' \<equiv> {a. \<forall>a' \<in> A'. A a a'}"

definition concurrency :: "('a, 's) lts \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"concurrency M con = (irreflp con \<and> (\<forall>p s s'. validfinpath M s p s' \<longrightarrow> (enabledactions M s \<inter> preimagerelation con (alloccurringactions (fin p)) \<subseteq> enabledactions M s')))"

definition JA :: "('a, 's) lts \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> ('a, 's) path \<Rightarrow> bool" where
"JA M con B s p = allsuffixes s p (\<lambda>s p. (\<forall>a \<in> enabledactions M s -B. (\<exists>a'. \<not>con a a' \<and> a' \<in> alloccurringactions p)))"

definition WHFA :: "('a, 's) lts \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> ('a, 's) path \<Rightarrow> bool" where
"WHFA M B s p = allsuffixes s p (\<lambda>s p. perpetuallyreachable M B s p -B \<subseteq> alloccurringactions p)"

definition SFA :: "('a, 's) lts \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> ('a, 's) path \<Rightarrow> bool" where
"SFA M B s p = allsuffixes s p (\<lambda>s p. relentlesslyenabled M s p -B \<subseteq> alloccurringactions p)"

definition SHFA :: "('a, 's) lts \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> ('a, 's) path \<Rightarrow> bool" where
"SHFA M B s p = allsuffixes s p (\<lambda>s p. relentlesslyreachable M B s p -B \<subseteq> alloccurringactions p)"

lemma WHFA_WFA : "WHFA M B s p \<Longrightarrow> WFA M B s p"
  unfolding WFA_def WHFA_def allsuffixes_def
  using perpetuallyenabled_perpetuallyreachable by fastforce

lemma SFA_WFA : "SFA M B s p \<Longrightarrow> WFA M B s p"
  unfolding SFA_def WFA_def allsuffixes_def
  using perpetuallyenabled_relentlesslyenabled by fastforce

lemma SHFA_SFA : "SHFA M B s p \<Longrightarrow> SFA M B s p"
  unfolding SFA_def SHFA_def allsuffixes_def using relentlesslyenabled_relentlesslyreachable by fastforce

text \<open>Defining the extension of a finite path.\<close>

fun extendfinpath :: "('a, 's) finpath \<Rightarrow> ('a, 's) path \<Rightarrow> ('a, 's) path" where
"extendfinpath p (fin p') = fin (p @ p')" |
"extendfinpath p (inf p') = inf (conc p p')"

lemma extendfinpath_pref_suff : "p = extendfinpath (pref i p) (suff i p)"
  by (cases p; simp)

lemma extendfinpath_extendfinpath [simp] : "extendfinpath (p @ p') p'' = extendfinpath p (extendfinpath p' p'')"
  by (cases p''; simp)

lemma extendfinemptypath [simp] : "extendfinpath [] p = p"
  by (cases p; simp)

lemma extendfinpath_ind [simp] : "i < length p \<Longrightarrow> ind i (extendfinpath p p') = p ! i" 
  by (cases p'; simp add: nth_append_left)

lemma extendfinpath_ind_right [simp] : "i \<ge> length p \<Longrightarrow> ind i (extendfinpath p p') = ind (i - length p) p'" 
  by (cases p'; simp add: nth_append_right)

lemma extendfinpath_pref [simp] : "i \<le> length p \<Longrightarrow> pref i (extendfinpath p p') = take i p" 
  by (cases p'; simp)

lemma extendfinpath_pref_right [simp] : "i > length p \<Longrightarrow> pref i (extendfinpath p p') = p @ pref (i - length p) p'" 
  by (cases p'; simp)

lemma extendfinpath_suff [simp] : "i < length p \<Longrightarrow> suff i (extendfinpath p p') = extendfinpath (drop i p) p'" 
  by (cases p'; simp)

lemma extendfinpath_suff_right [simp] : "i \<ge> length p \<Longrightarrow> suff i (extendfinpath p p') = suff (i - length p) p'" 
  by (cases p'; simp)

lemma validpathsplit: "validpath M s (extendfinpath p p') = (\<exists>s'. validfinpath M s p s' \<and> validpath M s' p')"
  using validfinpathsplit by (cases p'; simp; metis)

lemma occursleft : "occurs S' (fin p) \<Longrightarrow> occurs S' (extendfinpath p p')"
  by (cases p'; auto)

lemma occursright : "occurs S' p' \<Longrightarrow> occurs S' (extendfinpath p p')"
  by (cases p'; auto)

lemma occursfinleft : "occurs S' (fin (take i p)) \<Longrightarrow> occurs S' (fin p)"
  by (simp only: occursfinalternative, auto)

lemma notoccursfinright : "\<not>occurs S' (fin p) \<Longrightarrow> \<not>occurs S' (fin (drop i p))"
  by (simp only: occursfinalternative; simp)

lemma occursfinright : "occurs S' (fin (drop i p)) \<Longrightarrow> occurs S' (fin p)"
  using notoccursfinright by blast

lemma occursstateleft: "occursstate S' s (fin p) \<Longrightarrow> (occursstate S' s (extendfinpath p p'))"
  by (cases p'; auto)

lemma alloccurringstatesright: "alloccurringstates (laststate s p) p' \<subseteq> alloccurringstates s (extendfinpath p p')"
  by (cases p'; induct p; auto)

lemma occursstateright : "occursstate S' (laststate s p) p' \<Longrightarrow> occursstate S' s (extendfinpath p p')"
  unfolding occursstate_def using alloccurringstatesright insert_absorb insert_subset by metis

lemma occursleftorright :
  assumes "occurs A (fin p) \<or> occursstate S' s (fin p) \<or> occurs A p' \<or> occursstate S' (laststate s p) p'"
  shows "occurs A (extendfinpath p p') \<or> occursstate S' s (extendfinpath p p')" 
  using assms occursleft occursright occursstateleft occursstateright by metis
                                                      
lemma occursstaterightvalidpath : "validfinpath M s p s' \<and> occursstate S' s' p' \<Longrightarrow> occursstate S' s (extendfinpath p p')"
  using occursstateright validfinpathlaststate by metis

lemma occursempty : "occurs A (fin p) \<Longrightarrow> p \<noteq> []"
  by (cases p; simp)

lemma occursstateempty : "occursstate S' s (fin p) \<and> s \<notin> S' \<Longrightarrow> p \<noteq> []"
  by (cases p; simp)

lemma allnextstatesnotlocked: 
  assumes "S' = {s. \<nexists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> P s'}"
  and "s \<in> S'"
  and "validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p)"
  shows "alloccurringstates s (fin p) \<subseteq> S'"
  unfolding alloccurringstatesalternative
  apply rule
  using assms(2) apply auto
proof (rule ccontr)
  fix i
  assume "i < length p"
  hence validsubpath: "validfinpath M s (take (Suc i) p) (target (p!i)) \<and> \<not>occurs \<alpha>\<^sub>f (fin (take (Suc i) p))" using assms(3) validfinsubpathtarget occursfinleft by metis
  assume "target (p ! i) \<notin> S'"
  then obtain p' s'' where "validfinpath M (target (p ! i)) p' s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> P s''" using assms(1) by auto
  hence "validfinpath M s (take (Suc i) p @ p') s'' \<and> \<not>occurs \<alpha>\<^sub>f (fin (take (Suc i) p @ p')) \<and> P s''" using validsubpath by auto
  thus "False" using assms(1, 2) by blast
qed

lemma notlockedoccurs : "s \<in> {s. \<nexists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> P s'} \<and> validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<Longrightarrow> s' \<in> {s. \<nexists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> P s'}"
proof-
  assume assum1: "s \<in> {s. \<nexists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> P s'} \<and> validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p)"
  hence "alloccurringstates s (fin p) \<subseteq> {s. \<nexists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> P s'}" by (subst allnextstatesnotlocked[of _ M \<alpha>\<^sub>f P]; blast)
  moreover have "s' \<in> alloccurringstates s (fin p)" using assum1 laststateoccurs by metis
  ultimately show ?thesis by blast
qed

lemma notlocked : "s \<in> {s. \<nexists>p s'. validfinpath M s p s' \<and> P s'} \<and> validfinpath M s p s' \<Longrightarrow> s' \<in> {s. \<nexists>p s'. validfinpath M s p s' \<and> P s'}"
  by (insert notlockedoccurs[of s M "{}" P]; auto)

lemma occurringactionssubpath : "alloccurringactions p' \<subseteq> alloccurringactions (extendfinpath p p')"
  by (cases p'; induct p; auto)

lemma enabledactionssubset : "B \<subseteq> A \<Longrightarrow> enabledactionsset M A \<subseteq> enabledactionsset M B"
  by (auto simp: enabledactionsset_def)

lemma enabledactionsset_subpath: "laststate s p = s' \<Longrightarrow> enabledactionsset M (alloccurringstates s (extendfinpath p p')) \<subseteq> enabledactionsset M (alloccurringstates s' p')"
  using alloccurringstatesright enabledactionssubset by meson

lemma reachableactionsset_subpath: "laststate s p = s' \<Longrightarrow> reachableactionsset M B (alloccurringstates s (extendfinpath p p')) \<subseteq> reachableactionsset M B (alloccurringstates s' p')"
  using alloccurringstatesright reachableactionsstatessubset by meson

text \<open>Simplification rules for \<open>allsuffixes\<close>.\<close>

lemma allsuffixes_validinfpath : "validinfpath M s p \<Longrightarrow> allsuffixes s (inf p) P = (\<forall>i. P (source (p i)) (inf (suffix i p)))"
  apply (auto simp: allsuffixes_def validinfpath_def)
  using not0_implies_Suc suffix_0 apply metis
  using suffix_0 apply metis
  done

lemma suffixallsuffixesinf: "validinfpath M s p \<and> allsuffixes s (inf p) P \<Longrightarrow> allsuffixes (source (p n)) (inf (suffix n p)) P"
  unfolding allsuffixes_def by (cases n; simp add: validinfpath_def; auto)

lemma allsuffixesfinempty [simp] : "allsuffixes s (fin []) P = P s (fin [])" by (simp add: allsuffixes_def)

lemma allsuffixes_extendfinpath [simp] : "allsuffixes s (extendfinpath [t] p) P = (P s (extendfinpath [t] p) \<and> allsuffixes (target t) p P)" 
  apply (simp add: allsuffixes_def)
proof-
  have predextend: "\<And>Q. (\<forall>i\<in>indicespath (extendfinpath [t] p). i > 0 \<longrightarrow> Q i) = (\<forall>i\<in>indicespath p. Q (Suc i))" using gr0_conv_Suc by (cases p; auto)
  have "0 \<in> indicespath (extendfinpath [t] p)" by (cases p; simp)
  hence "(\<forall>i\<in>indicespath (extendfinpath [t] p). P (target (ind i (extendfinpath [t] p))) (suff (Suc i) (extendfinpath [t] p))) = (P (target (ind 0 (extendfinpath [t] p))) (suff (Suc 0) (extendfinpath [t] p)) \<and> (\<forall>i\<in>indicespath (extendfinpath [t] p). i > 0 \<longrightarrow> P (target (ind i (extendfinpath [t] p))) (suff (Suc i) (extendfinpath [t] p))))" using bot_nat_0.not_eq_extremum by blast
  moreover have "... = (P (target t) p \<and> (\<forall>i\<in>indicespath (extendfinpath [t] p). i > 0 \<longrightarrow> P (target (ind i (extendfinpath [t] p))) (suff (Suc i) (extendfinpath [t] p))))" by simp
  ultimately show "(P s (extendfinpath [t] p) \<and> (\<forall>i\<in>indicespath (extendfinpath [t] p). P (target (ind i (extendfinpath [t] p))) (suff i p))) = (P s (extendfinpath [t] p) \<and> P (target t) p \<and> (\<forall>i\<in>indicespath p. P (target (ind i p)) (suff (Suc i) p)))" using predextend by auto
qed

lemma allsuffixes_extendpath: "allsuffixes s (extendfinpath p p') P \<Longrightarrow> allsuffixes (laststate s p)  p' P"
  apply (induct p arbitrary: s)
  apply simp
proof-
  fix t p s
  assume IH : "\<And>s. allsuffixes s (extendfinpath p p') P \<Longrightarrow> allsuffixes (laststate s p) p' P"
  assume "allsuffixes s (extendfinpath (t # p) p') P"
  hence "allsuffixes s (extendfinpath [t] (extendfinpath p p')) P" by (cases p'; auto)
  hence "allsuffixes (target t) (extendfinpath p p') P" by simp
  thus "allsuffixes (laststate s (t # p)) p' P" using IH laststatetarget by metis
qed

lemma allsuffixes_extendpath_valid: "validfinpath M s p s' \<and> allsuffixes s (extendfinpath p p') P \<Longrightarrow> allsuffixes s' p' P"
  using allsuffixes_extendpath validfinpathlaststate by metis

lemma allsuffixes_extendpath_iff: 
  assumes "\<And>t p. t \<in> transition M \<and> allsuffixes (target t) p P \<Longrightarrow> P (source t) (extendfinpath [t] p)" 
  shows "validfinpath M s p s' \<Longrightarrow> allsuffixes s (extendfinpath p p') P = allsuffixes s' p' P"
  apply (rule iffI)
  using allsuffixes_extendpath_valid apply metis
  apply (induct p arbitrary: s)
  apply simp
proof-
  fix t p s
  assume IH: "\<And>s. validfinpath M s p s' \<Longrightarrow> allsuffixes s' p' P \<Longrightarrow> allsuffixes s (extendfinpath p p') P"
  assume "validfinpath M s (t # p) s'"
  moreover assume "allsuffixes s' p' P"
  ultimately have "s = source t \<and> t \<in> transition M \<and> allsuffixes (target t) (extendfinpath p p') P" using IH by simp
  moreover from this have "P s (extendfinpath [t] (extendfinpath p p'))" using assms by simp
  ultimately have "allsuffixes s (extendfinpath [t] (extendfinpath p p')) P" by simp
  thus "allsuffixes s (extendfinpath (t # p) p') P" by (cases p'; auto)
qed

lemma validfinpath_allsuffixes_empty: 
  assumes "\<And>t p. t \<in> transition M \<and> allsuffixes (target t) p P \<Longrightarrow> P (source t) (extendfinpath [t] p)" 
  shows "validfinpath M s p s' \<Longrightarrow> allsuffixes s (fin p) P = P s' (fin [])"
proof-
  assume "validfinpath M s p s'"
  hence "allsuffixes s (extendfinpath p (fin [])) P = P s' (fin [])" by (subst allsuffixes_extendpath_iff; simp add: assms)
  thus ?thesis by simp
qed

lemma P_extendpath:
  assumes "\<And>t p. t \<in> transition M \<and> validpath M (target t) p \<Longrightarrow> P (source t) (extendfinpath [t] p) = P (target t) p" 
  shows "validfinpath M s p s' \<and> validpath M s' p' \<Longrightarrow> P s (extendfinpath p p') =  P s' p'"
  apply (induct p arbitrary: s)
  apply simp
proof-
  fix t p s
  assume IH: "(\<And>s. validfinpath M s p s' \<and> validpath M s' p' \<Longrightarrow> P s (extendfinpath p p') = P s' p')"
  have "extendfinpath (t # p) p' = extendfinpath ([t] @ p) p'" by simp
  moreover have "... = extendfinpath [t] (extendfinpath p p')" using extendfinpath_extendfinpath by metis
  moreover assume "validfinpath M s (t # p) s' \<and> validpath M s' p'"
  ultimately show "P s (extendfinpath (t # p) p') = P s' p'" using IH assms validfinpath.simps(2) validpathsplit by metis
qed

lemma P_extendpath_notvalid:
  assumes "\<And>s t p. P s (extendfinpath [t] p) = P (target t) p" 
  shows "P s (extendfinpath p p') = P (laststate s p) p'"
  apply (induct p arbitrary: s)
  apply simp
proof-
  fix t p s
  assume IH: "(\<And>s. P s (extendfinpath p p') = P (laststate s p) p')"
  have "extendfinpath (t # p) p' = extendfinpath ([t] @ p) p'" by simp
  moreover have "... = extendfinpath [t] (extendfinpath p p')" using extendfinpath_extendfinpath by metis
  moreover have "laststate s (t # p) = laststate (target t) p" by (simp only: laststatetarget)
  ultimately show "P s (extendfinpath (t # p) p') = P (laststate s (t # p)) p'" using IH assms by metis
qed

text \<open>Continuing example of syntaxsemantics, giving a valid infinite path (from initial state)
  that satisfies \<open>B\<close>-WFA if and only if action \<open>\<b>\<close> is in \<open>B\<close>.\<close>

lemma example_inf_path : "validinfpath example_lts s\<^sub>0 (\<lambda>n. (s\<^sub>0, \<c>, s\<^sub>0))"
  by (simp add: validinfpath_def example_lts_def)

lemma example_WFA : "WFA example_lts B s\<^sub>0 (inf (\<lambda>n. (s\<^sub>0, \<c>, s\<^sub>0))) = (\<b> \<in> B)"
  by (auto simp: WFA_def perpetuallyenabled_alternative allsuffixes_def example_lts_def)

lemma example_inf_path' : "validinfpath example_lts s\<^sub>2 ([(s\<^sub>2, \<b>, s\<^sub>1), (s\<^sub>1, \<c>, s\<^sub>2)]\<^sup>\<omega>)"
  apply (auto simp: validinfpath_def example_lts_def)
proof-
  fix n
  assume "[(s\<^sub>2, \<b>, s\<^sub>1), (s\<^sub>1, \<c>, s\<^sub>2)] ! (n mod Suc (Suc 0)) \<noteq> (s\<^sub>2, \<b>, s\<^sub>1)"
  hence "n mod 2 \<noteq> 0" using nth_Cons_0 numeral_2_eq_2 by metis
  hence "n mod 2 = 1" by simp
  thus "[(s\<^sub>2, \<b>, s\<^sub>1), (s\<^sub>1, \<c>, s\<^sub>2)] ! (n mod Suc (Suc 0)) = (s\<^sub>1, \<c>, s\<^sub>2)" by (simp add: numeral_2_eq_2)
next
  fix n :: "nat"
  have "(n mod 2 = 0) \<or> (n mod 2 = 1)" by auto
  thus "target ([(s\<^sub>2, \<b>, s\<^sub>1), (s\<^sub>1, \<c>, s\<^sub>2)] ! (n mod Suc (Suc 0))) = source ([(s\<^sub>2, \<b>, s\<^sub>1), (s\<^sub>1, \<c>, s\<^sub>2)] ! (Suc n mod Suc (Suc 0)))" by (auto simp: numeral_2_eq_2 mod_Suc)
qed

(*contains lots of repetition due to lack of mod simplification rules*)
lemma example_WFA' : "WFA example_lts B s\<^sub>2 (inf [(s\<^sub>2, \<b>, s\<^sub>1), (s\<^sub>1, \<c>, s\<^sub>2)]\<^sup>\<omega>)"
  apply (auto simp: WFA_def allsuffixes_def example_lts_def perpetuallyenabled_def)
proof-
  have "\<b> = action ([(s\<^sub>2, \<b>, s\<^sub>1), (s\<^sub>1, \<c>, s\<^sub>2)] ! (0 mod Suc (Suc 0)))" by simp
  thus "\<b> \<in> action ` range (\<lambda>x. [(s\<^sub>2, \<b>, s\<^sub>1), (s\<^sub>1, \<c>, s\<^sub>2)] ! (x mod Suc (Suc 0)))" by blast
  fix i
  have "\<exists>x. Suc (i + x) mod Suc (Suc 0) = Suc 0" by presburger
  then obtain x where "Suc (i + x) mod Suc (Suc 0) = Suc 0" by auto
  hence "\<c> = action ([(s\<^sub>2, \<b>, s\<^sub>1), (s\<^sub>1, \<c>, s\<^sub>2)] ! (Suc (i + x) mod Suc (Suc 0)))" by simp
  thus "\<c> \<in> action ` range (\<lambda>x. [(s\<^sub>2, \<b>, s\<^sub>1), (s\<^sub>1, \<c>, s\<^sub>2)] ! (Suc (i + x) mod Suc (Suc 0)))" by blast
  thus "\<c> \<in> action ` range (\<lambda>x. [(s\<^sub>2, \<b>, s\<^sub>1), (s\<^sub>1, \<c>, s\<^sub>2)] ! (Suc (i + x) mod Suc (Suc 0)))" by assumption
  have "\<exists>x. Suc (i + x) mod Suc (Suc 0) = 0" by presburger
  then obtain x where "Suc (i + x) mod Suc (Suc 0) = 0" by metis
  hence "\<b> = action ([(s\<^sub>2, \<b>, s\<^sub>1), (s\<^sub>1, \<c>, s\<^sub>2)] ! (Suc (i + x) mod Suc (Suc 0)))" by simp
  thus "\<b> \<in> action ` range (\<lambda>x. [(s\<^sub>2, \<b>, s\<^sub>1), (s\<^sub>1, \<c>, s\<^sub>2)] ! (Suc (i + x) mod Suc (Suc 0)))" by blast
  thus "\<b> \<in> action ` range (\<lambda>x. [(s\<^sub>2, \<b>, s\<^sub>1), (s\<^sub>1, \<c>, s\<^sub>2)] ! (Suc (i + x) mod Suc (Suc 0)))" by assumption
  thus "\<b> \<in> action ` range (\<lambda>x. [(s\<^sub>2, \<b>, s\<^sub>1), (s\<^sub>1, \<c>, s\<^sub>2)] ! (Suc (i + x) mod Suc (Suc 0)))" by assumption
next
  fix i
  have "\<exists>x. Suc (i + x) mod Suc (Suc 0) = Suc 0" by presburger
  then obtain x where "Suc (i + x) mod Suc (Suc 0) = Suc 0" by blast
  moreover assume "\<forall>x. \<exists>s'. target ([(s\<^sub>2, \<b>, s\<^sub>1), (s\<^sub>1, \<c>, s\<^sub>2)] ! (Suc (i + x) mod Suc (Suc 0))) = s\<^sub>1 \<and> s' = s\<^sub>0 \<or> target ([(s\<^sub>2, \<b>, s\<^sub>1), (s\<^sub>1, \<c>, s\<^sub>2)] ! (Suc (i + x) mod Suc (Suc 0))) = s\<^sub>1 \<and> s' = s\<^sub>1"
  ultimately have "target ([(s\<^sub>2, \<b>, s\<^sub>1), (s\<^sub>1, \<c>, s\<^sub>2)] ! Suc 0) = s\<^sub>1" by metis
  thus "\<a> \<in> action ` range (\<lambda>x. [(s\<^sub>2, \<b>, s\<^sub>1), (s\<^sub>1, \<c>, s\<^sub>2)] ! (Suc (i + x) mod Suc (Suc 0)))" by simp
  thus "\<a> \<in> action ` range (\<lambda>x. [(s\<^sub>2, \<b>, s\<^sub>1), (s\<^sub>1, \<c>, s\<^sub>2)] ! (Suc (i + x) mod Suc (Suc 0)))" by assumption
qed

lemma WHFAempty : "WHFA M B s (fin []) = locked M B s" 
  apply (auto simp: WHFA_def locked_def perpetuallyreachable_def)
proof-
  fix a s'
  assume assum1: "reachableactions M B s \<subseteq> B"
  assume "(s, a, s') \<in> transition M"
  hence "validfinpath M s [] s \<and> \<not>occurs B (fin []) \<and> (s, a, s') \<in> transition M" by simp
  hence "a \<in> reachableactions M B s" unfolding reachableactions_def reachableactionsset_def enabledactions_def by blast
  thus "a \<in> B" using assum1 by auto
next
  fix a
  assume assum1: "{a. \<exists>s'. (s, a, s') \<in> transition M} \<subseteq> B"
  assume "a \<in> reachableactions M B s" 
  then obtain p s' where "validfinpath M s p s' \<and> \<not>occurs B (fin p) \<and> a \<in> enabledactions M s'" by (auto simp: reachableactions_def reachableactionsset_def)
  hence "\<exists>s'. (s, a, s') \<in> transition M" 
    apply (induct p)
    apply simp
    using assum1 apply (subgoal_tac "(s, action aa, target aa) \<in> transition M \<and> action aa \<in> -B"; (blast|auto))
    done
  thus "a \<in> B" using assum1 by blast
qed

text \<open>Simplification rules for generalization of SFA and SHFA.\<close>

lemma relentlessly_pred_sub: 
  assumes "A = (\<lambda>s p. {a. allsuffixes s p (\<lambda>s p. \<exists>s' \<in> alloccurringstates s p. Q a s')})"
  shows "A s (extendfinpath [t] p) \<subseteq> A (target t) p"
proof
  fix a
  assume "a \<in> A s (extendfinpath [t] p)"
  hence "allsuffixes s (extendfinpath [t] p) (\<lambda>s p. \<exists>s\<in>alloccurringstates s p. Q a s)" using assms by simp
  hence "allsuffixes (target t) p (\<lambda>s p. \<exists>s\<in>alloccurringstates s p. Q a s)" by auto
  thus "a \<in> A (target t) p" using assms by simp
qed

lemma relentlessly_pred_super: 
  assumes "A = (\<lambda>s p. {a. allsuffixes s p (\<lambda>s p. \<exists>s' \<in> alloccurringstates s p. Q a s')})"
  shows "A (target t) p \<subseteq> A s (extendfinpath [t] p)"
proof
  fix a
  assume "a \<in> A (target t) p"
  hence "allsuffixes (target t) p (\<lambda>s p. \<exists>s'\<in>alloccurringstates s p. Q a s')" using assms by simp
  moreover {
    from this obtain s' where "s' \<in> alloccurringstates (target t) p \<and> Q a s'" by (auto simp: allsuffixes_def)
    hence "\<exists>s'\<in>alloccurringstates s (extendfinpath [t] p). Q a s'" using alloccurringstatesright laststatesimps(1) in_mono by metis
  }
  ultimately have "allsuffixes s (extendfinpath [t] p) (\<lambda>s p. \<exists>s'\<in>alloccurringstates s p. Q a s')" by simp
  thus "a \<in> A s (extendfinpath [t] p)" using assms by simp
qed

lemma relentlessly_pred: 
  assumes "A = (\<lambda>s p. {a. allsuffixes s p (\<lambda>s p. \<exists>s' \<in> alloccurringstates s p. Q a s')})"
  shows "A s (extendfinpath [t] p) = A (target t) p "
  apply (rule subset_antisym)
  apply (rule relentlessly_pred_sub; simp add: assms)
  apply (rule relentlessly_pred_super; simp add: assms)
  done

lemma relentlessly_extendpath_pred: 
  assumes "A = (\<lambda>s p. {a. allsuffixes s p (\<lambda>s p. \<exists>s' \<in> alloccurringstates s p. Q a s')})"
  shows "validfinpath M s p s' \<Longrightarrow> A s (extendfinpath p p') = A s' p'"
proof-
  have "A s (extendfinpath p p') = A (laststate s p) p'" by (rule P_extendpath_notvalid [where ?P="A"]; (rule relentlessly_pred)?; simp add: assms)
  thus "validfinpath M s p s' \<Longrightarrow> A s (extendfinpath p p') = A s' p'" by (simp add: validfinpathlaststate) 
qed

lemma relentlessly_firststate :
  assumes "A = (\<lambda>s p. {a. allsuffixes s p (\<lambda>s p. \<exists>s' \<in> alloccurringstates s p. Q a s')})"
  shows  "A s (inf p) = A s' (inf p)"
proof-
  have "A s (inf p) = A s (extendfinpath [p 0] (inf (suffix (Suc 0) p)))" by simp
  moreover have "... = A (target (p 0)) (inf (suffix (Suc 0) p))" by (rule relentlessly_pred; simp add: assms)
  moreover have "A s' (extendfinpath [p 0] (inf (suffix (Suc 0) p))) = A (target (p 0)) (inf (suffix (Suc 0) p))" by (rule relentlessly_pred; simp add: assms)
  ultimately show ?thesis by simp
qed

lemma relentlessly_infextendpath: 
  assumes "A = (\<lambda>s p. {a. allsuffixes s p (\<lambda>s p. \<exists>s' \<in> alloccurringstates s p. Q a s')})"
  shows "A s (inf (conc p p')) = A s' (inf p')"
  apply (induct p)
  apply (simp; rule relentlessly_firststate[where ?s=s]; simp add: assms)
proof-
  fix t :: "'a \<times> 'b \<times> 'a"
  fix p
  assume "A s (inf (conc p p')) = A s' (inf p')"
  moreover have "A s (inf (conc p p')) = A (target t) (inf (conc p p'))" by (rule relentlessly_firststate[where ?s=s]; simp add: assms)
  moreover have "A s (extendfinpath [t] (inf (conc p p'))) = A (target t) (inf (conc p p'))" by (rule relentlessly_pred; simp add: assms)
  ultimately show "A s (inf (conc (t # p) p')) = A s' (inf p')" by simp
qed

lemma relentlessly_subpath :
  assumes "A = (\<lambda>s p. {a. allsuffixes s p (\<lambda>s p. \<exists>s' \<in> alloccurringstates s p. Q a s')})"
  and "P = (\<lambda>s p. allsuffixes s p (\<lambda>s p. A s p -B \<subseteq> alloccurringactions p))"
  shows "P s (extendfinpath [t] p) = P (target t) p"
  apply (auto simp: assms(2))
proof-
  fix a
  assume assum1: "allsuffixes (target t) p (\<lambda>s p. A s p -B\<subseteq> alloccurringactions p)"
  assume "a \<in> A s (extendfinpath [t] p)"
  moreover assume "a \<notin> B"
  moreover have "A s (extendfinpath [t] p) = A (target t) p" by (rule relentlessly_pred; simp add: assms)
  ultimately have "a \<in> A (target t) p -B" by simp
  hence "a \<in> alloccurringactions p" using assum1 by (auto simp: allsuffixes_def)
  thus "a \<in> alloccurringactions (extendfinpath [t] p)" using occurringactionssubpath subset_iff by meson
qed

lemma relentlessly_extendpath: 
  assumes "A = (\<lambda>s p. {a. allsuffixes s p (\<lambda>s p. \<exists>s' \<in> alloccurringstates s p. Q a s')})"
  and "P = (\<lambda>s p. allsuffixes s p (\<lambda>s p. A s p -B \<subseteq> alloccurringactions p))"
  shows "P (laststate s p) p' = P s (extendfinpath p p')"
proof-
  have "P s (extendfinpath p p') = P (laststate s p) p'" by (rule P_extendpath_notvalid; rule relentlessly_subpath; simp add: assms)
  thus ?thesis by simp
qed

lemma relentlessly_extendpath_valid:
  assumes "A = (\<lambda>s p. {a. allsuffixes s p (\<lambda>s p. \<exists>s' \<in> alloccurringstates s p. Q a s')})"
  and "P = (\<lambda>s p. allsuffixes s p (\<lambda>s p. A s p -B \<subseteq> alloccurringactions p))"
  shows "validfinpath M s p s' \<Longrightarrow> P s' p' = P s (extendfinpath p p')"
proof-
  have "P s (extendfinpath p p') = P (laststate s p) p'" by (rule P_extendpath_notvalid[of P], rule relentlessly_subpath[OF assms])
  thus "validfinpath M s p s' \<Longrightarrow> P s' p' = P s (extendfinpath p p')" by (simp add: validfinpathlaststate)
qed

lemma relentlessly_extendpath_inf:
  assumes "A = (\<lambda>s p. {a. allsuffixes s p (\<lambda>s p. \<exists>s' \<in> alloccurringstates s p. Q a s')})"
  and "P = (\<lambda>s p. allsuffixes s p (\<lambda>s p. A s p -B \<subseteq> alloccurringactions p))"
  shows "validfinpath M s p s' \<Longrightarrow> P s' (inf p') = P s (inf (conc p p'))"
  by (subst relentlessly_extendpath_valid[OF assms]; simp)

lemma relentlessly_infpathsuffix:
  assumes "A = (\<lambda>s p. {a. allsuffixes s p (\<lambda>s p. \<exists>s' \<in> alloccurringstates s p. Q a s')})"
  and "P = (\<lambda>s p. allsuffixes s p (\<lambda>s p. A s p -B \<subseteq> alloccurringactions p))"
  shows "validinfpath M s p \<Longrightarrow> P s (inf p) = P (source (p n)) (inf (suffix n p))"
proof-
  assume "validinfpath M s p"
  hence "validfinpath M s (prefix n p) (source (p n)) \<and> inf p = extendfinpath (prefix n p) (inf (suffix n p))" by simp
  moreover have "P (laststate s (prefix n p)) (inf (suffix n p)) = P s (extendfinpath (prefix n p) (inf (suffix n p)))" by (rule relentlessly_extendpath; simp add: assms)
  ultimately show "P s (inf p) = P (source (p n)) (inf (suffix n p))" using validfinpathlaststate by metis
qed

lemma lockednotreachable : "locked M B s \<Longrightarrow> \<forall>a\<in>-B. a \<notin> reachableactions M B s"
  apply rule+
proof-
  fix a
  assume locked: "locked M B s"
  assume Bcomp: "a \<in> -B"
  assume "a \<in> reachableactions M B s"
  then obtain p s' where validpath: "validfinpath M s p s' \<and> \<not>occurs B (fin p) \<and> a \<in> enabledactions M s'" by (auto simp: reachableactions_def reachableactionsset_def)
  {
    assume "p = []"
    hence "a \<in> enabledactions M s" using validpath by auto
    hence False using locked Bcomp unfolding locked_def by blast
  }
  moreover {
    fix t p'
    assume "p = t # p'"
    hence "(source t, action t, target t) \<in> transition M \<and> action t \<notin> B \<and> locked M B (source t)" using validpath locked by auto
    moreover from this have "\<exists>s'. (source t, action t, s') \<in> transition M" by blast
    ultimately have "False" unfolding locked_def enabledactions_def by auto
  }
  ultimately show False by (cases p)
qed

lemma notreachable_locked: "(\<forall>a\<in>-B. a \<notin> reachableactions M B s) \<Longrightarrow> locked M B s"
  unfolding locked_def apply (rule subsetI ballI)
proof-
  fix a
  assume assum1: "\<forall>a\<in>-B. a \<notin> reachableactions M B s"
  assume "a \<in> enabledactions M s"
  hence "a \<in> reachableactions M B s" using enabled_reachable subset_iff by metis
  thus "a \<in> B" using assum1 by auto
qed

lemma lockednotQ: 
  assumes "\<And>s a. a \<in> -B \<and> Q a s \<Longrightarrow> a \<in> reachableactions M B s"
  shows "a \<in> -B \<and> locked M B s \<Longrightarrow> \<not>Q a s" 
proof-
  fix a s
  assume "a \<in> -B \<and> locked M B s"
  hence "a \<in> -B \<and> a \<notin> reachableactions M B s" by (simp add: lockednotreachable)
  thus "\<not>Q a s" using assms by auto
qed

lemma relentlesslyinvarfin : 
  assumes "\<And>s a. a \<in> -B \<and> Q a s \<Longrightarrow> a \<in> reachableactions M B s" 
  and "\<And>s. (\<forall>a \<in> -B. \<not>Q a s) \<Longrightarrow> locked M B s"
  and "A = (\<lambda>s p. {a. allsuffixes s p (\<lambda>s p. \<exists>s' \<in> alloccurringstates s p. Q a s')})"
  and "P = (\<lambda>s p. allsuffixes s p (\<lambda>s p. A s p -B \<subseteq> alloccurringactions p))"
  shows "P s (fin []) = locked M B s"
  unfolding assms(3) assms(4) apply simp
proof-
  have "\<And>s. (\<forall>a \<in> -B. \<not>Q a s) = ({a. Q a s} -B = {})" by auto
  thus "({a. Q a s} \<subseteq> B) = locked M B s" using lockednotQ[OF assms(1)] assms by auto
qed

lemma occuringstatessuffix : "alloccurringstates (target (p n)) (inf (suffix (Suc n) p)) \<subseteq> alloccurringstates s (inf p)"
  by auto

lemma image_subset_inf : "n \<le> m \<Longrightarrow> image f (range (suffix m p)) \<subseteq> image f (range (suffix n p))"
  unfolding image_def apply auto
  using le_Suc_ex trans_le_add1 apply metis
  done

lemma image_subset_fin : "n \<le> m \<Longrightarrow> image f (set (drop m p)) \<subseteq> image f (set (drop n p))"
  unfolding image_def apply auto
  using set_drop_subset_set_drop subset_iff apply metis
  done

lemma occuringstatessuffixsuffix [simp] : "n \<le> m \<and> target (p m) \<in> alloccurringstates (target (p n)) (inf (suffix (Suc n) p)) \<Longrightarrow> alloccurringstates (target (p m)) (inf (suffix (Suc m) p)) \<subseteq> alloccurringstates (target (p n)) (inf (suffix (Suc n) p))"
proof-
  assume "n \<le> m \<and> target (p m) \<in> alloccurringstates (target (p n)) (inf (suffix (Suc n) p))" 
  hence "Suc n \<le> Suc m \<and> target (p m) \<in> insert (target (p n)) (image target (range (suffix (Suc n) p)))" by simp
  moreover from this have "image target (range (suffix (Suc m) p)) \<subseteq> image target (range (suffix (Suc n) p))" using image_subset_inf by metis
  ultimately have "insert (target (p m)) (image target (range (suffix (Suc m) p))) \<subseteq> insert (target (p n)) (image target (range (suffix (Suc n) p)))" by auto
  thus "alloccurringstates (target (p m)) (inf (suffix (Suc m) p)) \<subseteq> alloccurringstates (target (p n)) (inf (suffix (Suc n) p))" by simp
qed

lemma alloccurrinstatessuffixsuffixvalidinfpath:  "n \<le> m \<and> validinfpath M s p \<Longrightarrow> alloccurringstates (target (p m)) (inf (suffix (Suc m) p)) \<subseteq> alloccurringstates (target (p n)) (inf (suffix (Suc n) p))"
proof-
  assume "n \<le> m \<and> validinfpath M s p"
  hence "(n = m \<and> validinfpath M s p) \<or> n < m" by auto
  moreover have "n < m \<Longrightarrow> target (p m) \<in> alloccurringstates (target (p n)) (inf (suffix (Suc n) p))"
    unfolding alloccurringstatesalternative apply auto
    using less_natE apply metis
    done
  ultimately have "n \<le> m \<and> target (p m) \<in> alloccurringstates (target (p n)) (inf (suffix (Suc n) p))" by auto
  thus "alloccurringstates (target (p m)) (inf (suffix (Suc m) p)) \<subseteq> alloccurringstates (target (p n)) (inf (suffix (Suc n) p))" by (rule occuringstatessuffixsuffix)
qed

lemma somesuffix_actionrelentlessly :
  assumes "A = (\<lambda>s p. {a. allsuffixes s p (\<lambda>s p. \<exists>s' \<in> alloccurringstates s p. Q a s')})"
  shows "validinfpath M s p \<and> a \<notin> A s (inf p) \<Longrightarrow> (\<exists>n. alloccurringstates (source (p n)) (inf (suffix n p)) \<subseteq> {s. \<not>Q a s})"
proof-
  assume assum1: "validinfpath M s p \<and> a \<notin> A s (inf p)"
  hence "(\<forall>s \<in> alloccurringstates s (inf p). \<not>Q a s) \<or> (\<exists>i. \<forall>s \<in> alloccurringstates (target (p i)) (inf (suffix (Suc i) p)). \<not>Q a s)" unfolding assms allsuffixes_def by simp 
  moreover {
    assume "\<forall>s \<in> alloccurringstates s (inf p). \<not>Q a s"
    hence "alloccurringstates (source (p 0)) (inf (suffix 0 p)) \<subseteq> {s. \<not>Q a s}" using assum1 by (auto simp: validinfpath_def)
  }
  moreover {
    assume "\<exists>i. \<forall>s \<in> alloccurringstates (target (p i)) (inf (suffix (Suc i) p)). \<not>Q a s"
    hence "\<exists>i. alloccurringstates (source (p (Suc i))) (inf (suffix (Suc i) p)) \<subseteq> {s. \<not>Q a s}" using assum1 by (auto simp: validinfpath_def)
  }
  ultimately show "\<exists>n. alloccurringstates (source (p n)) (inf (suffix n p)) \<subseteq> {s. \<not>Q a s}" by blast
qed

lemma relentlesslreachable_onallsuffixes: "a \<in> relentlesslyreachable M B s p \<Longrightarrow> allsuffixes s p (\<lambda>s p. a \<in> relentlesslyreachable M B s p)"
  unfolding relentlesslyreachable_def allsuffixes_def
  apply (cases p; simp)
  apply (simp add: add.commute less_diff_conv)
  using add_Suc_right add_Suc_shift apply metis
  done

lemma relentlessly_onallsuffixes: 
  assumes "A = (\<lambda>s p. {a. allsuffixes s p (\<lambda>s p. \<exists>s' \<in> alloccurringstates s p. Q a s')})"
  shows "a \<in> A s p \<Longrightarrow> allsuffixes s p (\<lambda>s p. a \<in> A s p)"
  unfolding assms allsuffixes_def
  apply (cases p; simp)
  apply (simp add: add.commute less_diff_conv)
  using add_Suc_right add_Suc_shift apply metis
  done

lemma somesuffix_onlyrelentlessly :
  assumes "finite (-B)"
  and "A = (\<lambda>s p. {a. allsuffixes s p (\<lambda>s p. \<exists>s' \<in> alloccurringstates s p. Q a s')})"
  shows "validinfpath M s p \<Longrightarrow> (\<exists>n. allsuffixes (source (p n)) (inf (suffix n p)) (\<lambda>s p. {a. Q a s} -B \<subseteq> A s p))"
proof-
  assume assum1: "validinfpath M s p"
  have "\<exists>n. allsuffixes (source (p n)) (inf (suffix n p)) (\<lambda>s p. {a. Q a s} \<inter> -B \<subseteq> A s p)"
    apply (rule inductfiniteset[where ?A="-B"])
    apply (simp add: assms)
    apply (simp add: allsuffixes_def)
  proof-
    fix a A'
    assume "a \<in> - B - A' \<and> (\<exists>n. allsuffixes (source (p n)) (inf (suffix n p)) (\<lambda>s p. {a. Q a s} \<inter> A' \<subseteq> A s p))"
    then obtain n where assum2: "a \<in> - B - A' \<and> allsuffixes (source (p n)) (inf (suffix n p)) (\<lambda>s p. {a. Q a s} \<inter> A' \<subseteq> A s p)" by auto
    have "a \<in> A (source (p n)) (inf (suffix n p)) \<or> a \<notin> A (source (p n)) (inf (suffix n p))" by simp
    moreover {
      assume "a \<in> A (source (p n)) (inf (suffix n p))"
      hence "allsuffixes (source (p n)) (inf (suffix n p)) (\<lambda>s p. a \<in> A s p)" by (rule relentlessly_onallsuffixes[OF assms(2)])
      hence "allsuffixes (source (p n)) (inf (suffix n p)) (\<lambda>s p. {a. Q a s} \<inter> insert a A' \<subseteq> A s p)" using assum2 unfolding allsuffixes_def by blast
    }
    moreover {
      assume "a \<notin> A (source (p n)) (inf (suffix n p))"
      moreover have validsubpath: "validinfpath M (source (p n)) (suffix n p)" using assum1 by simp
      ultimately have "(\<exists>m. alloccurringstates (source ((suffix n p) m)) (inf (suffix m (suffix n p))) \<subseteq> {s. \<not>Q a s})" by (subst somesuffix_actionrelentlessly[OF assms(2)]; blast)
      then obtain m where anotenabled: "allsuffixes (source (p (n + m))) (inf (suffix (n + m) p)) (\<lambda>s p. \<not>Q a s)" unfolding alloccurringstatesalternative allsuffixes_def by auto
      have "allsuffixes (source ((suffix n p) m)) (inf (suffix m (suffix n p))) (\<lambda>s p. {a. Q a s} \<inter> A' \<subseteq> A s p)" apply (rule suffixallsuffixesinf) using validsubpath assum2 by blast
      hence "allsuffixes (source (p (n + m))) (inf (suffix (n + m) p)) (\<lambda>s p. {a. Q a s} \<inter> A' \<subseteq> A s p)" by simp
      hence "allsuffixes (source (p (n + m))) (inf (suffix (n + m) p)) (\<lambda>s p. {a. Q a s} \<inter> (insert a A') \<subseteq> A s p)" using anotenabled unfolding allsuffixes_def by simp
      hence "\<exists>n. allsuffixes (source (p n)) (inf (suffix n p)) (\<lambda>s p. {a. Q a s} \<inter> insert a A' \<subseteq> A s p)" by blast
    }
    ultimately show "\<exists>n. allsuffixes (source (p n)) (inf (suffix n p)) (\<lambda>s p. {a. Q a s} \<inter> insert a A' \<subseteq> A s p)" by blast
  qed
  moreover have "\<And>s. {a. Q a s} \<inter> -B = {a. Q a s} -B" by auto
  ultimately show ?thesis by auto
qed

lemma notfaircontradiction :
  assumes "\<not>allsuffixes s (inf p) (\<lambda>s p. Q s p \<subseteq> alloccurringactions p)"
  and "Q s (inf p) \<subseteq> Q (target (p 0)) (inf (suffix (Suc 0) p))"
  shows "\<exists>n a. a \<in> Q (target (p n)) (inf (suffix (Suc n) p)) \<and> a \<notin> alloccurringactions (inf (suffix (Suc n) p))"
proof-
  {
    assume "\<not> Q s (inf p) \<subseteq> alloccurringactions (inf p)"
    then obtain a where "a \<in> Q s (inf p) \<and> a \<notin> alloccurringactions (inf p)" by auto
    hence "a \<in> Q (target (p 0)) (inf (suffix (Suc 0) p)) \<and>  a \<notin> alloccurringactions (inf (suffix (Suc 0) p))" using assms by auto
    hence "\<exists>n a. a \<in> Q (target (p n)) (inf (suffix (Suc n) p)) \<and> a \<notin> alloccurringactions (inf (suffix (Suc n) p))" by blast
  }
  thus ?thesis using assms(1) unfolding allsuffixes_def by auto
qed

lemma P_alternative :
  assumes "A = (\<lambda>s p. {a. allsuffixes s p (\<lambda>s p. \<exists>s' \<in> alloccurringstates s p. Q a s')})"
  and "P = (\<lambda>s p. allsuffixes s p (\<lambda>s p. A s p -B \<subseteq> alloccurringactions p))"
  and "\<And>n a. a \<in> A (target (p n)) (inf (suffix (Suc n) p)) -B \<Longrightarrow> a \<in> alloccurringactions (inf (suffix (Suc n) p))"
  shows "P s (inf p)"
proof-
  have "A s (extendfinpath [p 0] (inf (suffix (Suc 0) p))) = A (target (p 0)) (inf (suffix (Suc 0) p))" by (rule relentlessly_pred; simp add: assms)
  hence "A s (inf p) \<subseteq> A (target (p 0)) (inf (suffix (Suc 0) p))" by simp
  hence "\<not>P s (inf p) \<Longrightarrow> \<exists>n a. a \<in> A (target (p n)) (inf (suffix (Suc n) p)) -B \<and> a \<notin> alloccurringactions (inf (suffix (Suc n) p))" unfolding assms(2) by (subst notfaircontradiction; auto)
  thus ?thesis using assms by auto
qed

text \<open>Defining violating paths, using \<open>freeuntiloccurrence\<close>.\<close>

definition freeuntiloccurrence :: "('a, 's) path \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
"freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e = ((\<exists>i. \<not>occurs \<alpha>\<^sub>f (fin (pref i p)) \<and> action (ind i p) \<in> \<alpha>\<^sub>e)
  \<or> \<not>occurs \<alpha>\<^sub>f p)"

definition violating :: "('a, 's) path \<Rightarrow> 'a rexp \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
"violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e = (\<exists>i. match \<rho> (pref i p) \<and> freeuntiloccurrence (suff i p) \<alpha>\<^sub>f \<alpha>\<^sub>e)"

lemma violatingempty [simp] : "violating p One \<alpha>\<^sub>f \<alpha>\<^sub>e = freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e"
proof-
  have "violating p One \<alpha>\<^sub>f \<alpha>\<^sub>e = (\<exists>i. (pref i p) = [] \<and> freeuntiloccurrence (suff i p) \<alpha>\<^sub>f \<alpha>\<^sub>e)" by (simp add : match_def violating_def)
  moreover have "... = (\<exists>i. (i = 0 \<or> p = fin []) \<and> freeuntiloccurrence (suff i p) \<alpha>\<^sub>f \<alpha>\<^sub>e)" by auto
  moreover have "... = (freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e)" using nosuffix by metis
  ultimately show ?thesis by auto
qed

text \<open>Definition of \<open>freeuntiloccurrence\<close> does not specify that \<open>i\<close> is within the length of the path.
But if the action occurs only outside the bound, then it does not occur.\<close>

lemma occursoutsidebound : 
  assumes "\<exists>i \<ge> length p'. \<not>occurs \<alpha>\<^sub>f (fin (take i p')) \<and> action (p'!i) \<in> \<alpha>\<^sub>e"
  shows "\<not>occurs \<alpha>\<^sub>f (fin p')"
  using assms take_all by metis

lemma freeuntiloccurrence_inbound : "freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e = (\<not>occurs \<alpha>\<^sub>f p \<or> (\<exists>i \<in> indicespath p. \<not>occurs \<alpha>\<^sub>f (fin (pref i p)) \<and> action (ind i p) \<in> \<alpha>\<^sub>e))"
  apply (cases p; simp add: freeuntiloccurrence_def del: occurssimps)
  using occursoutsidebound leI apply blast+
  done

text \<open>The existence of a progressing path that is \<open>\<alpha>\<^sub>f\<close> free until occurrence of \<open>\<alpha>\<^sub>e\<close> can be split into 4 cases.\<close>

lemma existfreeuntiloccurrenceprogressing_cases_pred [simp] :
  assumes "\<And>p s'. validfinpath M s p s' \<Longrightarrow> P s (fin p) = locked M B s'"
  shows "(\<exists>p. validpath M s p \<and> freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> P s p) = 
 ((\<exists>p' s'. validfinpath M s p' s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s') \<or> 
  (\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i < length p'. \<not>occurs \<alpha>\<^sub>f (fin (take i p')) \<and> action (p'!i) \<in> \<alpha>\<^sub>e) \<and> locked M B s') \<or>
  (\<exists>p'. validinfpath M s p' \<and> \<not>occurs \<alpha>\<^sub>f (inf p') \<and> P s (inf p')) \<or>
  (\<exists>p'. validinfpath M s p' \<and>  (\<exists>i. \<not>occurs \<alpha>\<^sub>f (fin (prefix i p')) \<and> action (p' i) \<in> \<alpha>\<^sub>e) \<and> P s (inf p')))"
  (is "?L = ?R")
proof
  assume ?L
  then obtain p where "validpath M s p \<and> freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> P s p" by auto
  hence assum1: "validpath M s p \<and> (\<not>occurs \<alpha>\<^sub>f p \<or> (\<exists>i \<in> indicespath p. \<not>occurs \<alpha>\<^sub>f (fin (pref i p)) \<and> action (ind i p) \<in> \<alpha>\<^sub>e)) \<and> P s p" using freeuntiloccurrence_inbound by auto
  {
    fix finp
    assume assum2: "p = fin finp"
    hence "validfinpath M s finp (laststate s finp) \<and> (\<not>occurs \<alpha>\<^sub>f (fin finp) \<or> (\<exists>i \<in> indicespath (fin finp). \<not>occurs \<alpha>\<^sub>f (fin (pref i (fin finp))) \<and> action (ind i (fin finp)) \<in> \<alpha>\<^sub>e)) \<and> locked M B (laststate s finp)" using assum1 validpath.simps(1) validfinpathlaststate assms by metis
    hence "validfinpath M s finp (laststate s finp) \<and> (\<not>occurs \<alpha>\<^sub>f (fin finp) \<or> (\<exists>i < length finp. \<not>occurs \<alpha>\<^sub>f (fin (take i finp)) \<and> action (finp!i) \<in> \<alpha>\<^sub>e)) \<and> locked M B (laststate s finp)" by auto
    hence ?R by blast
  }
  moreover {
    fix infp
    assume "p = inf infp"
    hence "validinfpath M s infp \<and> (\<not>occurs \<alpha>\<^sub>f (inf infp) \<or> (\<exists>i. \<not>occurs \<alpha>\<^sub>f (fin (prefix i infp)) \<and> action (infp i) \<in> \<alpha>\<^sub>e)) \<and> P s (inf infp)" using assum1 by auto
    hence ?R by blast
  }
  ultimately show ?R by (cases p)
next
  have "\<And>p s'. validfinpath M s p s' \<and> (\<not>occurs \<alpha>\<^sub>f (fin p) \<or> (\<exists>i<length p. \<not>occurs \<alpha>\<^sub>f (fin (take i p)) \<and> action (p ! i) \<in> \<alpha>\<^sub>e)) \<and> locked M B s' \<Longrightarrow> validpath M s (fin p) \<and> (\<not>occurs \<alpha>\<^sub>f (fin p) \<or>  (\<exists>i\<in>indicespath (fin p). \<not>occurs \<alpha>\<^sub>f (fin (pref i (fin p))) \<and> action (ind i (fin p)) \<in> \<alpha>\<^sub>e)) \<and> P s (fin p)" using assms by auto
  moreover have "\<And>p. validinfpath M s p \<and> (\<not>occurs \<alpha>\<^sub>f (inf p) \<or> (\<exists>i. \<not>occurs \<alpha>\<^sub>f (fin (prefix i p)) \<and> action (p i) \<in> \<alpha>\<^sub>e)) \<and> P s (inf p) \<Longrightarrow> validpath M s (inf p) \<and> (\<not>occurs \<alpha>\<^sub>f (inf p) \<or>  (\<exists>i\<in>indicespath (inf p). \<not>occurs \<alpha>\<^sub>f (fin (pref i (inf p))) \<and> action (ind i (inf p)) \<in> \<alpha>\<^sub>e)) \<and> P s (inf p)" by auto
  ultimately show "?R \<Longrightarrow> ?L" apply (simp only: freeuntiloccurrence_inbound) by blast
qed

lemma invariantextension_pred : 
  assumes "\<And>s. enabledactions M s = {} \<Longrightarrow> P s"
  and "\<nexists>p s'. validfinpath M s p s' \<and> P s'"
  shows "\<exists>a s'. (s, a, s') \<in> transition M \<and> (\<nexists>p s''. validfinpath M s' p s'' \<and> P s'')"
proof-
  have "enabledactions M s \<noteq> {}"
  proof
    assume "enabledactions M s = {}"
    hence "validfinpath M s [] s \<and> P s" using assms(1) by simp
    thus False using assms(2) by blast
  qed
  then obtain a s' where res1 : "(s, a, s') \<in> transition M" using actionenabled by metis
  let ?t = "(s, a, s')"
  have "\<nexists>p s''. validfinpath M s' p s'' \<and> P s''"
  proof
    assume "\<exists>p s''. validfinpath M s' p s'' \<and> P s''"
    then obtain p s'' where "validfinpath M s' p s'' \<and> P s''" by auto
    hence "validfinpath M s (?t # p) s'' \<and> P s''" using res1 by simp
    thus False using assms(2) by blast
  qed
  thus ?thesis using res1 by auto
qed

lemma invariantextension : 
  assumes "\<nexists>p s''. validfinpath M s p s'' \<and> enabledactions M s'' = {}"
  shows "\<exists>a s'. (s, a, s') \<in> transition M \<and> (\<nexists>p s''. validfinpath M s' p s'' \<and> enabledactions M s'' = {})"
  apply (rule invariantextension_pred)
  using assms apply blast+
  done

text \<open>Defining functions to structurally create infinite paths (that are complete)\<close>

abbreviation laststate_nonexhaustive :: "('a, 's) finpath \<Rightarrow> 's" where
"laststate_nonexhaustive p \<equiv> target (last p)"

lemma laststate_laststate_nonexhaustive : "p \<noteq> [] \<Longrightarrow> laststate s p = laststate_nonexhaustive p"
  by (cases p; simp)

function recursiveconcpaths :: "('s \<Rightarrow> ('a, 's) finpath) \<Rightarrow> 's \<Rightarrow> nat \<Rightarrow> 's \<times> 'a \<times> 's" where
"recursiveconcpaths succ s n = (if succ s = [] then undefined else (if n < length (succ s) then (succ s)!n else (recursiveconcpaths succ (laststate_nonexhaustive (succ s)) (n - length (succ s)))))"
  by auto
termination 
  apply (relation "measure (\<lambda>(succ,s,n). n)")
  apply auto
  apply (subgoal_tac "n > 0")
  apply simp
  using length_greater_0_conv apply fastforce
  done

fun ithpath :: "('s \<Rightarrow> ('a, 's) finpath) \<Rightarrow> 's \<Rightarrow> nat \<Rightarrow> ('a, 's) finpath" where
"ithpath succ s 0 = succ s" |
"ithpath succ s (Suc i) = succ (laststate_nonexhaustive (ithpath succ s i))"

lemma ithpath_right : "ithpath succ s (Suc i) = ithpath succ (laststate_nonexhaustive (succ s)) i"
  by (induct i; simp)

fun concipaths :: "('s \<Rightarrow> ('a, 's) finpath) \<Rightarrow> 's \<Rightarrow> nat \<Rightarrow> ('a, 's) finpath" where
"concipaths succ s 0 = []" |
"concipaths succ s (Suc i) = succ s @ concipaths succ (laststate_nonexhaustive (succ s)) i"

lemma concipaths_right : "concipaths succ s (Suc i) = concipaths succ s i @ ithpath succ s i"
  apply (induct i arbitrary: s)
  apply (simp)
  apply (simp add: ithpath_right del: ithpath.simps)
  done

lemma ithpath_somesucc : 
  assumes "s \<in> S' \<and> (\<forall>s \<in> S'. laststate_nonexhaustive (succ s) \<in> S')"
  shows "\<exists>s' \<in> S'. ithpath succ s i = succ s'"
  by (induct i; auto simp: assms)

lemma ithpath_laststate :
  assumes "s \<in> S' \<and> (\<forall>s \<in> S'. laststate_nonexhaustive (succ s) \<in> S')"
  shows "laststate_nonexhaustive (ithpath succ s i) \<in> S'"
  by (induct i; simp add: assms)

lemma predicate_ithpath : 
  assumes "P (succ s) \<and> s \<in> S' \<and> (\<forall>s \<in> S'. P (succ s) \<longrightarrow> P (succ (laststate_nonexhaustive (succ s))) \<and> laststate_nonexhaustive (succ s) \<in> S')"
  shows "P (ithpath succ s i)"
  apply (induct i)
  apply (simp add: assms)
proof-
  fix i
  have "P (ithpath succ s (Suc i)) \<and> laststate_nonexhaustive (ithpath succ s i) \<in> S'" by (induct i; simp add: assms)
  thus "P (ithpath succ s (Suc i))" by (simp add: assms)
qed

lemma ithpath_notempty : "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> laststate_nonexhaustive (succ s) \<in> S') \<longrightarrow> ithpath succ s i \<noteq> []"
  apply (induct i arbitrary : s)
  apply simp
   using ithpath_right apply metis
  done

lemma allithpath_notempty : "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> laststate_nonexhaustive (succ s) \<in> S') \<Longrightarrow> (\<forall>j < i. ithpath succ s j \<noteq> [])"
  using ithpath_notempty by metis

lemma lengthconcipaths : "(\<forall>j < i. ithpath succ s j \<noteq> []) \<longrightarrow> (length (concipaths succ s i)) \<ge> i"
  apply (induct i)
  apply simp
  apply (simp only : concipaths_right)
proof
  fix i
  assume IH : "(\<forall>j<i. ithpath succ s j \<noteq> []) \<longrightarrow> i \<le> length (concipaths succ s i)"
  assume assum1 : "\<forall>j<Suc i. ithpath succ s j \<noteq> []"
  hence "i \<le> length (concipaths succ s i)" using IH by auto
  moreover have "Suc 0 \<le> length (ithpath succ s i)" by (simp add: leI assum1)
  ultimately show "Suc i \<le> length (concipaths succ s i @ ithpath succ s i)" by auto
qed

lemma recursiveconcpaths_ithpath : "m = length (concipaths succ s i) \<and> k < length (ithpath succ s i) \<and> (\<forall>j \<le> i. ithpath succ s j \<noteq> []) \<Longrightarrow> recursiveconcpaths succ s (m + k) = (ithpath succ s i) ! k"
  apply (induct i arbitrary : m s)
  apply simp
proof-
  fix i m s
  assume IH : "(\<And>m s. m = length (concipaths succ s i) \<and> k < length (ithpath succ s i) \<and>  (\<forall>j\<le>i. ithpath succ s j \<noteq> []) \<Longrightarrow> recursiveconcpaths succ s (m + k) = ithpath succ s i ! k)" 
  assume assum1: "m = length (concipaths succ s (Suc i)) \<and> k < length (ithpath succ s (Suc i)) \<and> (\<forall>j\<le>Suc i. ithpath succ s j \<noteq> [])"
  hence "m + k \<ge> length (succ s) \<and> succ s \<noteq> []" by auto
  hence "recursiveconcpaths succ s (m + k) = recursiveconcpaths succ (laststate_nonexhaustive (succ s)) ((m - length (succ s)) + k)" using assum1 by auto
  moreover have "... = ithpath succ (laststate_nonexhaustive (succ s)) i ! k"
    apply (rule IH)
    using assum1 apply auto
    using ithpath_right assum1 Suc_le_mono apply metis+
    done
  moreover have "... = ithpath succ s (Suc i) ! k" by (simp only: ithpath_right)
  ultimately show "recursiveconcpaths succ s (m + k) = ithpath succ s (Suc i) ! k" by simp
qed

lemma take_all_but_last : "l \<noteq> [] \<Longrightarrow> (take (length l - 1) l) @ [l ! (length l - 1)] = l" 
proof-
  assume assum1: "l \<noteq> []"
  hence "(take (length l - 1) l) @ [l ! (length l - 1)] = (take (length l - 1) l) @ [hd (drop (length l - 1) l)]" by (simp add: hd_drop_conv_nth)
  moreover have "... = l" by (simp add: take_hd_drop assum1)
  ultimately show ?thesis by simp
qed

lemma subsequence_eq_list : "length l = (j - i) \<and> (\<forall>k. k\<ge>i \<and> k<j \<longrightarrow> w k = l!(k - i)) \<Longrightarrow> subsequence w i j = l"
  apply (simp add: subsequence_def)
  apply (induct j arbitrary: l; simp)
  apply auto
proof-
  fix j l 
  assume IH : "(\<And>l'. length l' = j - i \<and> (\<forall>k. i \<le> k \<and> k < j \<longrightarrow> l ! (k - i) = l' ! (k - i)) \<Longrightarrow> map w [i..<j] = l')"
  assume assum1: "length l = Suc j - i"
  hence "length (take (j - i) l) = j - i" by auto
  moreover have "\<forall>k. i \<le> k \<and> k < j \<longrightarrow> l ! (k - i) = (take (j - i) l) ! (k - i)" by auto
  ultimately have "map w [i..<j] = take (j - i) l" using IH by metis
  hence "map w [i..<j] @ [l ! (j - i)] = (take (j - i) l) @ [l ! (j - i)]" by auto
  moreover assume "i \<le> j"
  ultimately have "l \<noteq> [] \<and> map w [i..<j] @ [l ! (j - i)] = (take (length l - 1) l) @ [l ! (length l - 1)]" using assum1 by auto
  thus "map w [i..<j] @ [l ! (j - i)] = l" using assum1 take_all_but_last by metis
qed
  
lemma subsequence_recursiveconcpaths : "n = length (concipaths succ s i) \<and> k = length (ithpath succ s i) \<and> (\<forall>j \<le> i. ithpath succ s j \<noteq> []) \<Longrightarrow> subsequence (recursiveconcpaths succ s) n (n + k) = ithpath succ s i"
  apply (rule subsequence_eq_list)
proof-
  assume assum1: "n = length (concipaths succ s i) \<and> k = length (ithpath succ s i) \<and> (\<forall>j\<le>i. ithpath succ s j \<noteq> [])"
  have "(\<forall>m. n \<le> m \<and> m < n + k \<longrightarrow> recursiveconcpaths succ s m = ithpath succ s i ! (m - n))"
    apply (rule allI)
  proof
    fix m
    assume assum2: "n \<le> m \<and> m < n + k"
    hence "m - n < length (ithpath succ s i)" using assum1 by auto
    hence "recursiveconcpaths succ s (n + (m - n)) = (ithpath succ s i) ! (m - n)" using recursiveconcpaths_ithpath assum1 by metis
    thus "recursiveconcpaths succ s m = ithpath succ s i ! (m - n)" by (simp add: assum2)
  qed
  thus "length (ithpath succ s i) = n + k - n \<and> (\<forall>m. n \<le> m \<and> m < n + k \<longrightarrow> recursiveconcpaths succ s m = ithpath succ s i ! (m - n))" using assum1 by auto
qed

lemma existsconcipaths : "(\<forall>j < i. ithpath succ s j \<noteq> []) \<Longrightarrow> concipaths succ s i = prefix (length (concipaths succ s i)) (recursiveconcpaths succ s)"
  apply (induct i arbitrary: s)
  apply simp
   apply (simp only: concipaths_right)
proof-
  fix i s
  assume IH : "(\<And>s. (\<forall>j<i. ithpath succ s j \<noteq> []) \<Longrightarrow> concipaths succ s i = prefix (length (concipaths succ s i)) (recursiveconcpaths succ s))"
  assume assum1 : "(\<forall>j<Suc i. ithpath succ s j \<noteq> [])"
  hence "prefix (length (concipaths succ s i)) (recursiveconcpaths succ s) = concipaths succ s i" using IH by auto
  moreover have "prefix (length (concipaths succ s i @ ithpath succ s i)) (recursiveconcpaths succ s) = 
    (prefix (length (concipaths succ s i)) (recursiveconcpaths succ s)) @ (subsequence (recursiveconcpaths succ s) (length (concipaths succ s i)) (length (concipaths succ s i) + length (ithpath succ s i)))" 
    by (simp add: subsequence_append)
  moreover have "(subsequence (recursiveconcpaths succ s) (length (concipaths succ s i)) (length (concipaths succ s i) + length (ithpath succ s i))) = ithpath succ s i"
    by (simp add: assum1 subsequence_recursiveconcpaths)
  ultimately show "concipaths succ s i @ ithpath succ s i = prefix (length (concipaths succ s i @ ithpath succ s i)) (recursiveconcpaths succ s)" by auto
qed

lemma concipaths_nth : "(\<forall>j < i. ithpath succ s j \<noteq> []) \<and> n < i \<Longrightarrow> (concipaths succ s i) ! n = recursiveconcpaths succ s n"
proof-
  assume assum1 : "(\<forall>j < i. ithpath succ s j \<noteq> []) \<and> n < i"
  hence length : "length (concipaths succ s i) \<ge> i " by (simp add: lengthconcipaths)
  moreover have "concipaths succ s i = prefix (length (concipaths succ s i)) (recursiveconcpaths succ s)" using assum1 existsconcipaths by metis
  ultimately have "(concipaths succ s i) ! n = (prefix (length (concipaths succ s i)) (recursiveconcpaths succ s)) ! n" by simp
  moreover have "... = recursiveconcpaths succ s n" using length assum1 by auto
  ultimately show ?thesis by simp
qed

lemma suffix_recursiveconcpaths : "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> laststate_nonexhaustive (succ s) \<in> S') \<Longrightarrow> \<exists>s' \<in> S'. \<exists>j < length (succ s'). suffix i (recursiveconcpaths succ s) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate_nonexhaustive (succ s')))"
  apply (induct i)
proof-
  assume "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> laststate_nonexhaustive (succ s) \<in> S')"
  hence "succ s \<noteq> [] \<and> s \<in> S' \<and> suffix 0 (recursiveconcpaths succ s) = conc (drop 0 (succ s)) (recursiveconcpaths succ (laststate_nonexhaustive (succ s)))" by auto
  thus "\<exists>s' \<in> S'. \<exists>j < length (succ s'). suffix 0 (recursiveconcpaths succ s) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate_nonexhaustive (succ s')))" by blast
next
  fix i
  assume IH : "s \<in> S' \<and> (\<forall>s\<in>S'. succ s \<noteq> [] \<and> laststate_nonexhaustive (succ s) \<in> S') \<Longrightarrow> \<exists>s'\<in>S'. \<exists>j<length (succ s'). suffix i (recursiveconcpaths succ s) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate_nonexhaustive (succ s')))"
  moreover assume assum1: "s \<in> S' \<and> (\<forall>s\<in>S'. succ s \<noteq> [] \<and> laststate_nonexhaustive (succ s) \<in> S')"
  ultimately obtain j s' where "s' \<in> S' \<and> j < length (succ s') \<and> suffix i (recursiveconcpaths succ s) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate_nonexhaustive (succ s')))" by auto
  moreover have "Suc i = i + 1" by auto
  ultimately have res1: "s' \<in> S' \<and> j < length (succ s') \<and> suffix (Suc i) (recursiveconcpaths succ s) = suffix 1 (conc (drop j (succ s')) (recursiveconcpaths succ (laststate_nonexhaustive (succ s'))))" using suffix_suffix by metis
  hence "length (succ s') = Suc j \<or> length (succ s') > Suc j" by auto
  moreover {
    assume assum2: "length (succ s') = Suc j"
    hence "suffix (Suc i) (recursiveconcpaths succ s) = recursiveconcpaths succ (laststate_nonexhaustive (succ s'))" using res1 by simp
    moreover have "... = conc (drop 0 (succ (laststate_nonexhaustive (succ s')))) (recursiveconcpaths succ (laststate_nonexhaustive (succ (laststate_nonexhaustive (succ s')))))" using res1 assum1 by auto
    moreover have "0 < length (succ (laststate_nonexhaustive (succ s'))) \<and> laststate_nonexhaustive (succ s') \<in> S'" using res1 assum1 by auto
    ultimately have "\<exists>s'\<in>S'. \<exists>j < length (succ s'). suffix (Suc i) (recursiveconcpaths succ s) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate_nonexhaustive (succ s')))" by metis
  }
  moreover {
    assume "length (succ s') > Suc j"
    moreover have "s' \<in> S' \<and> suffix (Suc i) (recursiveconcpaths succ s) =  conc (drop (Suc j) (succ s')) (recursiveconcpaths succ (laststate_nonexhaustive (succ s')))" using Suc_le_eq res1 by auto
    ultimately have "\<exists>s'\<in>S'. \<exists>j < length (succ s'). suffix (Suc i) (recursiveconcpaths succ s) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate_nonexhaustive (succ s')))" by auto
  }
  ultimately show "\<exists>s'\<in>S'. \<exists>j < length (succ s'). suffix (Suc i) (recursiveconcpaths succ s) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate_nonexhaustive (succ s')))" by auto
qed

lemma suffix_recursiveconcpathslaststate : "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> laststate s (succ s) \<in> S') \<Longrightarrow> \<exists>s' \<in> S'. \<exists>j < length (succ s'). suffix i (recursiveconcpaths succ s) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate s' (succ s')))"
proof-
  assume assum1: "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> laststate s (succ s) \<in> S')"
  hence "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> laststate_nonexhaustive (succ s) \<in> S')" using laststate_laststate_nonexhaustive by metis
  then obtain s' j where "s' \<in> S' \<and> j < length (succ s') \<and> suffix i (recursiveconcpaths succ s) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate_nonexhaustive (succ s')))" using suffix_recursiveconcpaths by metis
  moreover from this have "laststate_nonexhaustive (succ s') = laststate s' (succ s')" using laststate_laststate_nonexhaustive assum1 by metis
  ultimately show "\<exists>s' \<in> S'. \<exists>j < length (succ s'). suffix i (recursiveconcpaths succ s) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate s' (succ s')))" by auto
qed

lemma suffix_recursiveconcpathsrelentlessly : 
  assumes "A = (\<lambda>s p. {a. allsuffixes s p (\<lambda>s p. \<exists>s' \<in> alloccurringstates s p. Q a s')})"
  shows "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> laststate_nonexhaustive (succ s) \<in> S') \<and> a \<in> A (target (recursiveconcpaths succ s n)) (inf (suffix (Suc n) (recursiveconcpaths succ s))) \<Longrightarrow> \<exists>s' p. s' \<in> S' \<and> a \<in> A s' (inf (recursiveconcpaths succ s')) \<and> suffix (Suc n) (recursiveconcpaths succ s) = conc p (recursiveconcpaths succ s')"
proof-
  assume "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> laststate_nonexhaustive (succ s) \<in> S') \<and> a \<in> A (target (recursiveconcpaths succ s n)) (inf (suffix (Suc n) (recursiveconcpaths succ s)))"
  hence assum1: "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> laststate s (succ s) \<in> S') \<and> a \<in> A (target (recursiveconcpaths succ s n)) (inf (suffix (Suc n) (recursiveconcpaths succ s)))" using laststate_laststate_nonexhaustive by metis
  then obtain s' j where assum2: "s' \<in> S' \<and> j < length (succ s') \<and> suffix (Suc n) (recursiveconcpaths succ s) = conc (drop j (succ s')) (recursiveconcpaths succ (laststate s' (succ s')))" using suffix_recursiveconcpathslaststate by metis
  moreover have "A (target (recursiveconcpaths succ s n)) (inf (conc (drop j (succ s')) (recursiveconcpaths succ (laststate s' (succ s'))))) = A (laststate s' (succ s')) (inf (recursiveconcpaths succ (laststate s' (succ s'))))" by (rule relentlessly_infextendpath[OF assms])
  ultimately have "a \<in> A (laststate s' (succ s')) (inf (recursiveconcpaths succ (laststate s' (succ s'))))" using assum1 by metis
  thus "\<exists>s' p. s' \<in> S' \<and> a \<in> A s' (inf (recursiveconcpaths succ s')) \<and> suffix (Suc n) (recursiveconcpaths succ s) = conc p (recursiveconcpaths succ s')" using assum1 assum2 by auto
qed

lemma unfoldrecursiveconcpaths : 
  assumes "succ s \<noteq> []"
  shows "recursiveconcpaths succ s = conc (succ s) (recursiveconcpaths succ (laststate_nonexhaustive (succ s)))"     
  using assms by auto

lemma source_eq_target :
  assumes "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> (source ((succ s) ! 0)) = s \<and> laststate_nonexhaustive (succ s) \<in> S')"
  shows "laststate_nonexhaustive (ithpath succ s n) \<in> S' \<and> source ((ithpath succ s (Suc n)) ! 0) = laststate_nonexhaustive (ithpath succ s n)"
  apply (induct n)
  apply (simp add: assms)
   unfolding ithpath.simps using assms apply blast
  done

lemma lasttarget_eq_targetithpath : 
  assumes "ithpath succ s n \<noteq> []"
  shows "laststate_nonexhaustive (concipaths succ s (Suc n)) = laststate_nonexhaustive (ithpath succ s n)"
  by (simp add: concipaths_right assms del: concipaths.simps)

lemma laststate_suc :
  "((\<lambda>s. laststate_nonexhaustive (succ s)) ^^ Suc n) s = ((\<lambda>s. laststate_nonexhaustive (succ s)) ^^ n) (laststate_nonexhaustive (succ s))"
  by (induct n; simp)

lemma validinfpathconc :
  "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> (\<exists>s' \<in> S'. validfinpath M s (succ s) s')) \<Longrightarrow> validinfpath M s (recursiveconcpaths succ s)"
  apply (simp add: validinfpath_def del: recursiveconcpaths.simps)
proof
  assume "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> (\<exists>s' \<in> S'. validfinpath M s (succ s) s'))"
  hence assum1 : "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> validfinpath M s (succ s) (laststate_nonexhaustive (succ s)) \<and> laststate_nonexhaustive (succ s) \<in> S')" using validfinpathlaststate laststate_laststate_nonexhaustive by metis
  have "s = source ((succ s)!0)" using validfinpathsource assum1 by metis
  thus "s = source (recursiveconcpaths succ s 0)" using assum1 by simp
  have res1: "\<forall>n. \<exists>s' \<in> S'. validfinpath M s (concipaths succ s n) s'"
  proof
    fix n
    have "s \<in> S' \<longrightarrow> (\<exists>s' \<in> S'. validfinpath M s (concipaths succ s n) s')" by (induct n arbitrary: s; simp; metis assum1)
    thus "\<exists>s' \<in> S'. validfinpath M s (concipaths succ s n) s'" using assum1 by simp
  qed
  show "\<forall>n. recursiveconcpaths succ s n \<in> transition M \<and> target (recursiveconcpaths succ s n) = source (recursiveconcpaths succ s (Suc n))"
  proof
    fix n
    have allnonempty : "(\<forall>j<Suc (Suc n). ithpath succ s j \<noteq> [])" using allithpath_notempty assum1 by metis
    hence "Suc (Suc n) \<le> length (concipaths succ s (Suc (Suc n)))" by (simp only : lengthconcipaths)
    hence "n < length (concipaths succ s (Suc (Suc n))) \<and> Suc n < length (concipaths succ s (Suc (Suc n)))" by arith
    hence "(concipaths succ s (Suc (Suc n)))!n \<in> transition M \<and> target ((concipaths succ s (Suc (Suc n)))! n) = source ((concipaths succ s (Suc (Suc n)))!(Suc n))" using ithtransitionfinpath ithtargetsourcefinpath res1 by metis
    moreover have "Suc n < Suc (Suc n) \<and> n < Suc (Suc n)" by auto
    moreover from this allnonempty have "recursiveconcpaths succ s (Suc n) = (concipaths succ s (Suc (Suc n)))!(Suc n) \<and> recursiveconcpaths succ s n = (concipaths succ s (Suc (Suc n)))! n" by (simp only: concipaths_nth)
    ultimately show "recursiveconcpaths succ s n \<in> transition M \<and> target (recursiveconcpaths succ s n) = source (recursiveconcpaths succ s (Suc n))" by simp
  qed
qed

lemma successorlemma :
  assumes "s \<in> S' \<and> (\<forall>s'. s' \<in> S' \<longrightarrow> (\<exists>t. source t = s' \<and> P t \<and> t \<in> transition M \<and> target t \<in> S'))"
  shows "(\<exists> p. validinfpath M s p \<and> (\<forall>n. P (p n)))"
proof-
  from assms obtain succ where assum1: "\<forall>s'. s' \<in> S' \<longrightarrow> source (succ s') = s' \<and> P (succ s') \<and> (succ s') \<in> transition M \<and> target (succ s') \<in> S'" by metis
  let ?p = "recursiveconcpaths (\<lambda>s'. [succ s']) s"
  have "validinfpath M s ?p" by (rule validinfpathconc [where ?S'=S']; simp add: assum1 assms)
  moreover {
    fix n
    have "s \<in> S' \<longrightarrow> P (?p n)" by (induct n arbitrary: s; simp add: assum1)
  }
  ultimately have "validinfpath M s ?p \<and> (\<forall>n. P (?p n))" using assms by simp
  thus ?thesis by auto
qed

lemma successorlemma_no_pred : 
  assumes "s \<in> S' \<and> (\<forall>s'. s' \<in> S' \<longrightarrow> (\<exists>t. source t = s' \<and> t \<in> transition M \<and> target t \<in> S'))"
  shows "\<exists>p. validinfpath M s p"
  using assms by (insert successorlemma[of s _ "\<lambda>n. True"]; auto)

lemma validpredconc :
  assumes "\<And>p p'. Q s p \<and> Q (laststate s p) p' \<Longrightarrow> Q s (p @ p')"
  and "\<And>p n. n < length p \<and> Q s p \<Longrightarrow> P s (p ! n)"
  shows "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> Q s (succ s) \<and> laststate_nonexhaustive (succ s) \<in> S') \<Longrightarrow> (\<forall>n. P s (recursiveconcpaths succ s n))"
proof
  assume assum1 : "s \<in> S' \<and> (\<forall>s \<in> S'. succ s \<noteq> [] \<and> Q s (succ s) \<and> laststate_nonexhaustive (succ s) \<in> S')"
  fix n
  have res1: "Q s (concipaths succ s (Suc n))"
    apply (induct n, simp add: assum1)
  proof-
    fix n
    have "ithpath succ s n \<noteq> []" by (subst ithpath_notempty [where ?S'=S']; simp add: assum1)
    hence "laststate_nonexhaustive (concipaths succ s (Suc n)) = laststate_nonexhaustive (ithpath succ s n)" using lasttarget_eq_targetithpath by simp
    moreover have "laststate_nonexhaustive (ithpath succ s n) \<in> S'" using ithpath_laststate assum1 by metis
    ultimately have "Q (laststate_nonexhaustive (concipaths succ s (Suc n))) (ithpath succ s (Suc n))" using assum1 by auto
    moreover have "concipaths succ s (Suc n) \<noteq> []" using assum1 by simp
    moreover assume "Q s (concipaths succ s (Suc n))"
    ultimately have "Q s (concipaths succ s (Suc n) @ ithpath succ s (Suc n))" using assms(1) laststate_laststate_nonexhaustive by metis
    thus "Q s (concipaths succ s (Suc (Suc n)))" using concipaths_right by metis
  qed
  have "(\<forall>j<Suc n. ithpath succ s j \<noteq> [])" using assum1 ithpath_notempty by metis
  moreover have "n < Suc n" by auto
  ultimately have "recursiveconcpaths succ s n = (concipaths succ s (Suc n)) ! n \<and> length (concipaths succ s (Suc n)) \<ge> Suc n" using concipaths_nth lengthconcipaths by metis
  moreover have "n < length (concipaths succ s (Suc n)) \<Longrightarrow> P s ((concipaths succ s (Suc n)) ! n)" using assms(2) res1 by blast
  ultimately show "P s (recursiveconcpaths succ s n)" by auto
qed

lemma exists_extensionpath :
  "(\<exists>p s'. validfinpath M s p s' \<and> enabledactions M s' = {}) \<or> (\<exists>p. validinfpath M s p)"
proof-
  have "(\<nexists>p s'. validfinpath M s p s' \<and> enabledactions M s' = {}) \<Longrightarrow> (\<exists>p. validinfpath M s p)"
  proof-
    assume assum1: "\<nexists>p s'. validfinpath M s p s' \<and> enabledactions M s' = {}"
    let ?S' = "{s. \<nexists>p s'. validfinpath M s p s' \<and> enabledactions M s' = {}}"
    have res1: "s \<in> ?S'" using assum1 by auto
    have res2: "\<forall>s'. s' \<in> ?S' \<longrightarrow> (\<exists>t. source t = s' \<and> t \<in> transition M \<and> target t \<in> ?S')" using assum1 invariantextension by auto
    show "\<exists>p. validinfpath M s p"
      apply (rule successorlemma_no_pred)
      using res1 res2 apply blast
      done
  qed
  thus ?thesis by blast
qed  

text \<open>Simplifications for valid progressing paths that are complete. These can be split into different cases.\<close>

lemma splitvalidfinpath_notoccursenabled : 
  assumes feasible: "\<And>s'. (\<exists>p' s''. validfinpath M s' p' s'' \<and> locked M B s'') \<or> (\<exists>p'. validinfpath M s' p' \<and> P s' (inf p'))"
  and extendinfpath: "\<And>s' p p'. validfinpath M s p s' \<and> validinfpath M s' p' \<Longrightarrow> P s' (inf p') = P s (inf (conc p p'))"
  shows "(\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> enabled M s' \<alpha>\<^sub>e) =
  ((\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i < length p'. \<not>occurs \<alpha>\<^sub>f (fin (take i p')) \<and> action (p'!i) \<in> \<alpha>\<^sub>e) \<and> locked M B s') \<or>
  (\<exists>p'. validinfpath M s p' \<and>  (\<exists>i. \<not>occurs \<alpha>\<^sub>f (fin (prefix i p')) \<and> action (p' i) \<in> \<alpha>\<^sub>e) \<and> P s (inf p')))" 
  (is "?L = (?R1 \<or> ?R2)")
proof
  {
    assume ?R1
    then obtain p' s' i where assum1 : "i < length p' \<and> validfinpath M s p' s' \<and> \<not>(occurs \<alpha>\<^sub>f (fin (take i p'))) \<and> action (p'!i) \<in> \<alpha>\<^sub>e \<and> locked M B s'" by auto
    have "action (p'!i) \<in> \<alpha>\<^sub>e \<and> (source (p'!i), action (p'!i), target (p'!i)) \<in> transition M" using assum1 by auto
    hence "enabled M (source (p'!i)) \<alpha>\<^sub>e" by (simp add: enabled_def; blast)
    moreover have "validfinpath M s (take i p') (source (p'!i)) \<and> \<not>(occurs \<alpha>\<^sub>f (fin (take i p')))" using assum1 by auto
    ultimately have ?L by auto   
  }
  moreover {
    assume ?R2
    then obtain p' i where assum1 : "validinfpath M s p' \<and>  \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and>  action (p' i) \<in> \<alpha>\<^sub>e" by auto
    hence "p' i \<in> transition M \<and> action (p' i) \<in> \<alpha>\<^sub>e" using validinfpath_def by metis
    hence "(source (p' i), action (p' i), target (p' i)) \<in> transition M \<and> action (p' i) \<in> \<alpha>\<^sub>e" by simp
    hence "enabled M (source (p' i)) \<alpha>\<^sub>e" by (simp add: enabled_def; blast)
    hence "validfinpath M s (prefix i p') (source (p' i)) \<and> \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and> enabled M (source (p' i)) \<alpha>\<^sub>e" using assum1 validinfsubpath by metis
    hence ?L by blast
  }
  ultimately show "(?R1 \<or> ?R2) \<Longrightarrow> ?L" by blast
next
  assume ?L
  then obtain p s' s'' a where assum1: "validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> a \<in> \<alpha>\<^sub>e \<and> (s', a, s'') \<in> transition M" by (auto simp: enabled_def)
  let ?t = "(s', a, s'')"
  let ?p = "p@[?t]"
  have validfinpath : "validfinpath M s ?p s''" using assum1 by simp
  have "(\<exists>p' s'''. validfinpath M s'' p' s''' \<and> locked M B s''') \<or> (\<exists>p'. validinfpath M s'' p' \<and> P s'' (inf p'))" using feasible by auto
  moreover {
    assume "\<exists>p' s'''. validfinpath M s'' p' s''' \<and> locked M B s'''"
    then obtain p' s''' where "validfinpath M s'' p' s''' \<and> locked M B s'''" by auto
    hence "validfinpath M s (?p@p') s''' \<and> locked M B s'''" using validfinpath by simp 
    moreover have "length p < length (?p@p') \<and> \<not>(occurs \<alpha>\<^sub>f (fin (take (length p) (?p@p')))) \<and> action ((?p@p')!(length p)) \<in> \<alpha>\<^sub>e" using assum1 by simp
    ultimately have ?R1 by blast
  }
  moreover {
    assume "\<exists>p'. validinfpath M s'' p' \<and> P s'' (inf p')"
    then obtain p' where "validinfpath M s'' p' \<and> P s'' (inf p')" by auto
    hence "validinfpath M s (conc ?p p') \<and> P s (inf (conc ?p p'))" using validinfpathsplit validfinpath extendinfpath by metis
    hence "validinfpath M s (conc ?p p') \<and> P s (inf (conc ?p p')) \<and> \<not>(occurs \<alpha>\<^sub>f (fin (prefix (length p) (conc ?p p')))) \<and> action ((conc ?p p') (length p)) \<in> \<alpha>\<^sub>e" using assum1 by simp
    hence ?R2 by blast
  }
  ultimately show "?R1 \<or> ?R2" by auto
qed

lemma freeuntiloccurrenceprogressing_lockedenabled_pred: 
  assumes feasible: "\<And>s'. (\<exists>p' s''. validfinpath M s' p' s'' \<and> locked M B s'') \<or> (\<exists>p'. validinfpath M s' p' \<and> P s' (inf p'))"
  and extendpath: "\<And>s' p p'. validfinpath M s p s' \<and> validpath M s' p' \<Longrightarrow> P s (extendfinpath p p') = P s' p'"
  and locking: "\<And>s. locked M B s = P s (fin [])"
  shows "(\<exists>p. validpath M s p \<and> freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> P s p) = 
  ((\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e))
  \<or> (\<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p)))"
proof-
  have "(\<exists>p. validpath M s p \<and> freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> P s p) = 
  ((\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s')
  \<or> (\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> enabled M s' \<alpha>\<^sub>e)
  \<or> (\<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p) \<and> P s (inf p)))"
    apply (subst existfreeuntiloccurrenceprogressing_cases_pred[where?B=B])
    using locking extendpath apply force
    apply (subst splitvalidfinpath_notoccursenabled[where ?P = P])
    using feasible apply blast
    using extendpath apply force
    apply blast
    done
  thus ?thesis by blast
qed

lemma freeuntiloccurrenceprogressing_lockedenabled: "(\<exists>p. validpath M s p \<and> freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M B s p) = 
  ((\<exists>p s'. validfinpath M s p s' \<and> \<not>occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> enabled M s' \<alpha>\<^sub>e))
  \<or> (\<exists>p. validinfpath M s p \<and> \<not>occurs \<alpha>\<^sub>f (inf p)))"
  apply (subst freeuntiloccurrenceprogressing_lockedenabled_pred [of _ B]; simp?)
proof-
  fix p'
  show "\<And>s' p. validfinpath M s p s' \<and> validpath M s' p' \<Longrightarrow> progressing M B s (extendfinpath p p') = progressing M B s' p'"
    apply (cases p'; simp) using validfinpathlaststate by metis
next
  fix s
  have "(\<exists>p s'. validfinpath M s p s' \<and> enabledactions M s' = {}) \<or> (\<exists>p. validinfpath M s p)" by (rule exists_extensionpath)
  moreover have "\<And>s. enabledactions M s = {} \<Longrightarrow> locked M B s" unfolding locked_def by auto
  ultimately show "(\<exists>p s'. validfinpath M s p s' \<and> locked M B s') \<or> (\<exists>p. validinfpath M s p)" by blast
qed
 
lemma splitviolating_predicate [simp] : 
  assumes extendpath: "\<And>p p' s'. validfinpath M s p s' \<and> validpath M s' p' \<Longrightarrow> P s' p' = P s (extendfinpath p p')"
  shows "(\<exists>p. validpath M s p \<and> violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> P s p) = 
  (\<exists>p p' s'. validfinpath M s p s' \<and> match \<rho> p  \<and> validpath M s' p' \<and> freeuntiloccurrence p' \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> P s' p')"
  (is "?L = ?R")
proof
  assume ?L
  hence "\<exists>p i s'. validfinpath M s (pref i p) s' \<and> match \<rho> (pref i p) \<and> validpath M s' (suff i p) \<and> freeuntiloccurrence (suff i p) \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> P s (extendfinpath (pref i p) (suff i p))" unfolding violating_def using extendfinpath_pref_suff validpathsplit by metis
  hence "\<exists>p i s'. validfinpath M s (pref i p) s' \<and> match \<rho> (pref i p) \<and> validpath M s' (suff i p) \<and> freeuntiloccurrence (suff i p) \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> P s' (suff i p)" using extendpath by metis
  thus ?R by auto
next
  assume ?R
  then obtain p p' s' where assum1: "validfinpath M s p s' \<and> match \<rho> p \<and> validpath M s' p' \<and> freeuntiloccurrence p' \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> P s' p'" by auto
  hence "match \<rho> (pref (length p) (extendfinpath p p')) \<and> freeuntiloccurrence (suff (length p) (extendfinpath p p')) \<alpha>\<^sub>f \<alpha>\<^sub>e" by simp
  moreover have "validpath M s (extendfinpath p p') \<and> P s (extendfinpath p p')" using assum1 extendpath validpathsplit by metis
  ultimately show ?L unfolding violating_def by blast
qed

lemma splitviolating : "(\<exists>p. validpath M s p \<and> violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M B s p) =
  (\<exists>p p' s'. validfinpath M s p s' \<and> match \<rho> p \<and> validpath M s' p' \<and> freeuntiloccurrence p' \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M B s' p')"
  apply (rule splitviolating_predicate)
proof-
  fix p'
  show "\<And>p s'. validfinpath M s p s' \<and> validpath M s' p' \<Longrightarrow> progressing M B s' p' = progressing M B s (extendfinpath p p')" by (cases p'; auto simp: validfinpathlaststate)
qed

end