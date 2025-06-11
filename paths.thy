theory paths
imports syntaxsemantics "HOL-Library.Omega_Words_Fun"
begin

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
"validfinpath M s (t#ts) s' = (s = source t  \<and> t \<in> transition M \<and> validfinpath M (target t) ts s')"

definition validinfpath :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> ('a, 's) infpath \<Rightarrow> bool" where
"validinfpath M s p = (s = source (p 0) \<and> (\<forall>n. p n \<in> transition M \<and> (target (p n) = source (p (Suc n)))))"

text \<open>A path is either a finite path or an infinite path.\<close>

datatype ('a, 's) path = fin "('a, 's) finpath" | inf "('a, 's) infpath"

definition enabledactions :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> 'a set" where
"enabledactions M s = {a . (\<exists>s'. (s, a, s') \<in> transition M)}"

lemma actionenabled : "enabledactions M s \<noteq> {} = (\<exists>a s'. (s, a, s') \<in> transition M)"
  by (simp add: enabledactions_def)

definition locked :: "('a, 's) lts \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> bool" where
"locked M B s = (enabledactions M s \<subseteq> B)"

fun progressing :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> 'a set \<Rightarrow> ('a, 's) path \<Rightarrow> bool" where
"progressing M s B (fin p) = (\<exists>s'. validfinpath M s p s' \<and> locked M B s')" |
"progressing M s B (inf p) = validinfpath M s p"

text \<open>A finite path matches a regular formula if and only if its sequence of actions is in the language 
of the regular formula.\<close>

definition match :: "'a regularformula \<Rightarrow> ('a, 's) finpath \<Rightarrow> bool" where
"match \<rho> p = (map action p \<in> regformtolanguage \<rho>)"

text \<open>A finite path matches a regular formula n times if and only if its sequence of actions is in the 
language of the regular formula concatenated n times.\<close>

fun matchntimes :: "nat \<Rightarrow> 'a regularformula \<Rightarrow> ('a, 's) finpath \<Rightarrow> bool" where
"matchntimes 0 R p = (p = [])" |
"matchntimes (Suc n) R p = (\<exists>p' p''. p = p' @ p'' \<and> match R p' \<and> matchntimes n R p'')"

lemma existsninduct [simp] : "((\<exists>n. P (Suc n)) \<or> P 0) = (\<exists>n. P n)"
  using zero_induct by blast

text \<open>A finite path \<open>p\<close> matches \<open>repeat R\<close> (Kleene star) if and only if there exists \<open>n\<close> such that 
\<open>p\<close> matches \<open>R\<close> \<open>n\<close> times.\<close>

lemma matchrepeat_eq_matchntimes : "match (repeat R) p = (\<exists>n. matchntimes n R p)"
proof-
  have "match (repeat R) p = (map action p \<in> (\<Union>n. (regformtolanguage R) ^^ n))" by (simp add: match_def)
  moreover have "... = (\<exists>n. map action p \<in> (regformtolanguage R) ^^ n)" by auto
  moreover have "\<forall>n. (map action p \<in> (regformtolanguage R) ^^ n) = (matchntimes n R p)"
  proof
    fix n
    show "(map action p \<in> (regformtolanguage R) ^^ n) = (matchntimes n R p)"
    apply (induct n arbitrary : p; simp)
    proof-
    fix n
    fix p :: "('a, 's) finpath"
    assume assum1 : "(\<And>(p :: ('a, 's) finpath). (map action p \<in> regformtolanguage R ^^ n) = matchntimes n R p)"
    have "(map action p \<in> regformtolanguage R @@ regformtolanguage R ^^ n) = (\<exists>p' p''. p = p' @ p'' \<and>  ((map action p') \<in> regformtolanguage R) \<and> ((map action p'') \<in> regformtolanguage R ^^ n))" by (rule conclem'')
    moreover have "... = (\<exists>p' p''. p = p'@p'' \<and>  match R p' \<and>  matchntimes n R p'')" using assum1 by (auto simp: match_def) 
    ultimately show "(map action p \<in> regformtolanguage R @@ regformtolanguage R ^^ n) = (\<exists>p' p''. p = p' @ p'' \<and> match R p' \<and> matchntimes n R p'')" by simp
  qed
  qed
  ultimately show ?thesis by blast
qed

text \<open>Simplifications of match for all patterns of regular formulas.\<close>

lemma matchunfold [simp] : 
  shows "match eps p = (p = [])"
  and "match (acts A) p = (\<exists>t. p = [t] \<and> action t \<in> A)"
  and "match (after R Q) p = (\<exists>p' p''. p = p' @ p'' \<and> match R p' \<and> match Q p'')"
  and "match (union R Q) p = (match R p \<or> match Q p)"
  and "match (repeat R) p = (\<exists>n. matchntimes n R p)"
  prefer 5
  apply (rule matchrepeat_eq_matchntimes)
  apply (simp_all add: match_def)
  apply (rule iffI; auto)
  apply (rule iffI; metis append_eq_map_conv)
  done

text \<open>A finite path matches \<open>repeat (acts A)\<close> (A Kleene star) if and only if 
  all its actions are in \<open>A\<close>.\<close>

lemma matchrepeatact : "match (repeat (acts A)) p = (set (map action p) \<subseteq> A)"
  apply (induction p; simp)
  apply (rule exI)
  apply (subgoal_tac "matchntimes 0 (acts A) []")
  apply blast
  apply simp
  apply (rule iffI)
proof-
  fix t 
  fix p :: "('a, 's) finpath"
  assume assum1: "(\<exists>n. matchntimes n (acts A) p) = (action ` set p \<subseteq> A)"
  assume "\<exists>n. matchntimes n (acts A) (t # p)"
  from this obtain n where "matchntimes n (acts A) (t # p)" by auto
  thus "action t \<in> A \<and> action ` set p \<subseteq> A" 
    apply (induct n)
    apply (simp)
    using assum1 apply force
    done
next
  fix t :: "'s \<times> 'a \<times> 's" 
  fix p :: "('a, 's) finpath"
  assume "(\<exists>n. matchntimes n (acts A) p) = (action ` set p \<subseteq> A)"
  from this obtain n where assum1: "matchntimes n (acts A) p = (action ` set p \<subseteq> A)" by auto
  assume "action t \<in> A \<and> action ` set p \<subseteq> A"
  hence "t # p = [t] @ p \<and> action t \<in> A \<and> matchntimes n (acts A) p" using assum1 by simp
  hence "matchntimes (Suc n) (acts A) (t # p)" unfolding matchntimes.simps matchunfold by blast 
  thus "\<exists>n. matchntimes n (acts A) (t # p)" by blast
qed

fun pref :: "nat \<Rightarrow> ('a, 's) path \<Rightarrow> ('a, 's) finpath" where 
"pref i (fin p) = take i p" |
"pref i (inf p) = prefix i p"

fun suff :: "nat \<Rightarrow> ('a, 's) path \<Rightarrow> ('a, 's) path" where 
"suff i (fin p) = fin (drop i p)" |
"suff i (inf p) = inf (suffix i p)"

fun ind :: "nat \<Rightarrow> ('a, 's) path \<Rightarrow> ('s \<times> 'a \<times> 's)" where 
"ind i (fin p) = p!i" |
"ind i (inf p) = p i"

lemma prefixleft : "(prefix (Suc n) p) = (p 0)#(prefix n (suffix (Suc 0) p))"
  by (induct n; simp)

lemma validfinpathsplit [simp] : "(\<exists>s''. validfinpath M s p s'' \<and> validfinpath M s'' p' s') = validfinpath M s (p @ p') s'"
  by (induct p arbitrary: s; simp)

lemma shiftinfvalidpath [simp]: "(validinfpath M s (t ## p)) = (s = source t \<and> t \<in> transition M \<and> validinfpath M (target t) p)"
proof-
  have "(\<forall>n. (n = 0 \<longrightarrow> t \<in> transition M \<and> target t = source (p 0)) \<and> (0 < n \<longrightarrow> p (n - Suc 0) \<in> transition M \<and> target (p (n - Suc 0)) = source (p n))) =
    (t \<in> transition M \<and> target t = source (p 0) \<and> (\<forall>n. (0 < n \<longrightarrow> p (n - Suc 0) \<in> transition M \<and> target (p (n - Suc 0)) = source (p n))))" by auto
  moreover have "... = (t \<in> transition M \<and> target t =  source (p 0) \<and> (\<forall>n. p n \<in> transition M \<and> target (p n) = source (p (Suc n))))" by auto
  ultimately have "(validinfpath M s (conc [t] p)) = (s = source t \<and> t \<in> transition M \<and> validinfpath M (target t) p)" by (simp add: validinfpath_def conc_def)
  thus ?thesis by simp
qed

lemma validinfpathsplit [simp] : "(\<exists>s'. validfinpath M s p s' \<and> validinfpath M s' p') = validinfpath M s (conc p p')"
  by (induction p arbitrary: s; simp)

lemma validfinsubpath [simp] : "i < length p \<and> validfinpath M s p s' \<Longrightarrow> validfinpath M s (take i p) (source (p!i))"
  apply (induct p arbitrary: s i)
  apply (simp)
proof-
  case Cons
  then show ?case by (cases i) auto
qed

lemma validfinsubpathright [simp] : "i < length p \<and> validfinpath M s p s' \<Longrightarrow> validfinpath M (source (p!i)) (drop i p) s'"
  apply (induct p arbitrary: s i)
  apply (simp)
proof-
  case Cons
  then show ?case by (cases i) auto
qed
 
lemma validinfsubpath : "validinfpath M s p \<Longrightarrow> (validfinpath M s (prefix i p) (source (p i)))"
  apply (induct i arbitrary : s p; simp add: validinfpath_def)
  apply (metis validfinpath.simps validfinpathsplit)
  done

lemma validinfsubpathright [simp] : "validinfpath M s p \<Longrightarrow> validinfpath M (source (p i)) (suffix i p)"
  by (induct i; simp add: validinfpath_def)

text \<open>A set of actions \<open>A\<close> occurs on path \<open>p\<close> if and only if there exists an action in A 
that occurs along the path.\<close>

fun occurs :: "'a set \<Rightarrow> ('a, 's) path \<Rightarrow> bool" where
"occurs A (fin p) = (\<exists> a \<in> A. a \<in> (set (map action p)))" |
"occurs A (inf p) = (\<exists> n. (action (p n)) \<in> A)" 

fun indicespath :: "('a, 's) path \<Rightarrow> nat set" where
"indicespath (fin p) = ({n. n < length p})" |
"indicespath (inf p) = UNIV"

fun freeuntiloccurrence :: "('a, 's) path \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
"freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e = ((\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (pref i p))) \<and> action (ind i p) \<in> \<alpha>\<^sub>e)
  \<or> \<not>(occurs \<alpha>\<^sub>f p))"

fun violating :: "('a, 's) path \<Rightarrow> 'a regularformula \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
"violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e = (\<exists>i. match \<rho> (pref i p) \<and> freeuntiloccurrence (suff i p) \<alpha>\<^sub>f \<alpha>\<^sub>e)"

lemma emptylist [simp] : "(pref i p = []) = (i = 0 \<or> p = fin [])"
  using take_eq_Nil by (cases p) simp_all

lemma emptypath : "p = [] \<and> validfinpath M s p s' \<Longrightarrow> (s' = s)"
  by (induct p; simp)

lemma nosuffix : "(p = fin [] \<or> i = 0) \<Longrightarrow> (suff i p = p)"
  by (cases p) auto

lemma violatingempty [simp] : "violating p eps \<alpha>\<^sub>f \<alpha>\<^sub>e = freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e"
proof-
  have "violating p eps \<alpha>\<^sub>f \<alpha>\<^sub>e = (\<exists>i. (pref i p) = [] \<and> freeuntiloccurrence (suff i p) \<alpha>\<^sub>f \<alpha>\<^sub>e)" by (simp add : match_def)
  moreover have "... = (\<exists>i. (i = 0 \<or> p = fin []) \<and> freeuntiloccurrence (suff i p) \<alpha>\<^sub>f \<alpha>\<^sub>e)" by auto
  moreover have "... = (freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e)" using nosuffix by metis
  ultimately show ?thesis by auto
qed

text \<open>Definition of \<open>freeuntiloccurrence\<close> does not specify that \<open>i\<close> is within the length of the path.\<close>

lemma occursoutsidebound : 
  assumes "(\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i \<ge> length p'. \<not>(occurs \<alpha>\<^sub>f (fin (take i p'))) \<and> action (p'!i) \<in> \<alpha>\<^sub>e) \<and> locked M B s')"
  shows "\<exists>p' s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s'"
proof-
  from assms obtain p' s' i where assum1 : "validfinpath M s p' s' \<and> i \<ge> length p' \<and> \<not>(occurs \<alpha>\<^sub>f (fin (take i p'))) \<and> action (p'!i) \<in> \<alpha>\<^sub>e \<and> locked M B s'" by auto
  hence "validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin (take i p')) \<and> locked M B s'" using assum1 by blast
  moreover have "take i p' = p'" using assum1 by simp
  ultimately have "validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s'" by auto
  thus ?thesis by auto
qed 

text \<open>A progressing path that is \<open>\<alpha>\<^sub>f\<close> free until occurrence of \<open>\<alpha>\<^sub>e\<close> can be split into 4 cases.\<close>

lemma unfoldcases [simp] : "(\<exists> p. freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p) = 
 ((\<exists>p' s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s') \<or> 
  (\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i < length p'. \<not>(occurs \<alpha>\<^sub>f (fin (take i p'))) \<and> action (p'!i) \<in> \<alpha>\<^sub>e) \<and> locked M B s') \<or>
  (\<exists>p'. validinfpath M s p' \<and> \<not> occurs \<alpha>\<^sub>f (inf p')) \<or>
  (\<exists>p'. validinfpath M s p' \<and>  (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and> action (p' i) \<in> \<alpha>\<^sub>e)))"
proof
  assume "\<exists>p. freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p"
  from this obtain p where assum1 : "freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p" by auto
  have "(freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p) = ((\<exists>p' s'. p = fin p' \<and>  validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s') \<or> 
  (\<exists>p' s'.  p = fin p' \<and> validfinpath M s p' s' \<and> (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (take i p'))) \<and> action (p'!i) \<in> \<alpha>\<^sub>e) \<and> locked M B s') \<or>
  (\<exists>p'. p = inf p' \<and>  validinfpath M s p' \<and> \<not> occurs \<alpha>\<^sub>f (inf p')) \<or>
  (\<exists>p'. p = inf p' \<and> validinfpath M s p' \<and>  (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and> action (p' i) \<in> \<alpha>\<^sub>e)))"
    apply (cases p)
    apply auto
    done
  hence "((\<exists>p' s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s') \<or>
  (\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (take i p'))) \<and> action (p'!i) \<in> \<alpha>\<^sub>e) \<and> locked M B s') \<or>
  (\<exists>p'. validinfpath M s p' \<and> \<not> occurs \<alpha>\<^sub>f (inf p')) \<or>
  (\<exists>p'. validinfpath M s p' \<and>  (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and> action (p' i) \<in> \<alpha>\<^sub>e)))" using assum1 by blast
  hence "((\<exists>p' s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s') \<or>
  (\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i < length p'. \<not>(occurs \<alpha>\<^sub>f (fin (take i p'))) \<and> action (p'!i) \<in> \<alpha>\<^sub>e) \<and> locked M B s') \<or>
  (\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i \<ge> length p'. \<not>(occurs \<alpha>\<^sub>f (fin (take i p'))) \<and> action (p'!i) \<in> \<alpha>\<^sub>e) \<and> locked M B s') \<or>
  (\<exists>p'. validinfpath M s p' \<and> \<not> occurs \<alpha>\<^sub>f (inf p')) \<or>
  (\<exists>p'. validinfpath M s p' \<and>  (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and> action (p' i) \<in> \<alpha>\<^sub>e)))" by (meson linorder_le_less_linear)
  moreover have "(\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i \<ge> length p'. \<not>(occurs \<alpha>\<^sub>f (fin (take i p'))) \<and> action (p'!i) \<in> \<alpha>\<^sub>e) \<and> locked M B s') \<Longrightarrow>
    (\<exists>p' s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s')" by (rule occursoutsidebound) 
  ultimately show "((\<exists>p' s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s') \<or>
  (\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i < length p'. \<not>(occurs \<alpha>\<^sub>f (fin (take i p'))) \<and> action (p'!i) \<in> \<alpha>\<^sub>e) \<and> locked M B s') \<or>
  (\<exists>p'. validinfpath M s p' \<and> \<not> occurs \<alpha>\<^sub>f (inf p')) \<or>
  (\<exists>p'. validinfpath M s p' \<and>  (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and> action (p' i) \<in> \<alpha>\<^sub>e)))"  by auto
next
  assume "(\<exists>p' s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s') \<or>
    (\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i < length p'. \<not> occurs \<alpha>\<^sub>f (fin (take i p')) \<and> action (p' ! i) \<in> \<alpha>\<^sub>e) \<and> locked M B s') \<or>
    (\<exists>p'. validinfpath M s p' \<and> \<not> occurs \<alpha>\<^sub>f (inf p')) \<or>
    (\<exists>p'. validinfpath M s p' \<and> (\<exists>i. \<not> occurs \<alpha>\<^sub>f (fin (prefix i p')) \<and> action (p' i) \<in> \<alpha>\<^sub>e))"
  moreover { 
    assume "\<exists>p' s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s'"
    from this obtain p' where "\<exists>s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s'" by auto
    hence "freeuntiloccurrence (fin p') \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B (fin p')" by auto 
    hence "\<exists>p. freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p" by blast
  }
  moreover { 
    assume "\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i < length p'. \<not> occurs \<alpha>\<^sub>f (fin (take i p')) \<and> action (p' ! i) \<in> \<alpha>\<^sub>e) \<and> locked M B s'"
    from this obtain p' where "\<exists>s'. validfinpath M s p' s' \<and> (\<exists>i. \<not> occurs \<alpha>\<^sub>f (fin (take i p')) \<and> action (p' ! i) \<in> \<alpha>\<^sub>e) \<and> locked M B s'" by auto
    hence "freeuntiloccurrence (fin p') \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B (fin p')" by auto 
    hence "\<exists>p. freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p" by blast
  }
  moreover { 
    assume "\<exists>p'. validinfpath M s p' \<and> \<not> occurs \<alpha>\<^sub>f (inf p')"
    from this obtain p' where "validinfpath M s p' \<and> \<not> occurs \<alpha>\<^sub>f (inf p')" by auto
    hence "freeuntiloccurrence (inf p') \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B (inf p')" by auto 
    hence "\<exists>p. freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p" by blast
  }
  moreover { 
    assume "\<exists>p'. validinfpath M s p' \<and> (\<exists>i. \<not> occurs \<alpha>\<^sub>f (fin (prefix i p')) \<and> action (p' i) \<in> \<alpha>\<^sub>e)"
    from this obtain p' where "validinfpath M s p' \<and> (\<exists>i. \<not> occurs \<alpha>\<^sub>f (fin (prefix i p')) \<and> action (p' i) \<in> \<alpha>\<^sub>e)" by auto
    hence "freeuntiloccurrence (inf p') \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B (inf p')" by auto 
    hence "\<exists>p. freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p" by blast
  }
  ultimately show "\<exists>p. freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p" by blast
qed

lemma zerothtransitionfinpath : "0 < length p \<and> validfinpath M s p s' \<Longrightarrow> (p!0 \<in> transition M)"
  by (induction p; simp)

text \<open>The \<open>i\<close>'th transition in a valid path is in the transitions of the labeled transition system\<close>
(*maybe do this for source and target too*)
lemma ithtransitionfinpath [simp] : "i < length p \<and> validfinpath M s p s' \<Longrightarrow> (p!i \<in> transition M)"
proof-
  assume assum1: "i < length p \<and> validfinpath M s p s'"
  hence "0 < length (drop i p) \<and> validfinpath M (source (p!i)) (drop i p) s'" by auto
  hence "(drop i p)!0 \<in> transition M" by (rule zerothtransitionfinpath)
  moreover have "(drop i p)!0 = p!i" using assum1 by auto
  ultimately show ?thesis by simp
qed

fun extendfinpath :: "('a, 's) finpath \<Rightarrow> ('a, 's) path \<Rightarrow> ('a, 's) path" where
"extendfinpath p (fin p') = fin (p @ p')" |
"extendfinpath p (inf p') = inf (conc p p')"

lemma extendfinemptypath [simp] : "(extendfinpath [] p) = p"
  by (cases p; simp)

text \<open>shiftinfpath puts a transition before an infinite path (extendfinpath [t] p).\<close>
definition shiftinfpath :: "('s \<times> 'a \<times> 's) \<Rightarrow> ('a, 's) infpath \<Rightarrow> ('a, 's) infpath" where
"shiftinfpath t p i = (if (i = 0) then t else p(i - Suc 0))"

lemma prefixextendinfpath [simp]: "prefix (Suc i) (t ## p) = t # (prefix i p)"
  by (induct i; simp)

lemma invariantextension : 
  assumes "\<forall>s. (enabledactions M s = {}) \<longrightarrow> P s"
  and "(\<nexists>finextension s''. validfinpath M s (finextension) s'' \<and> P s'')"
  shows "\<exists>a s'. (s, a, s') \<in> transition M \<and> (\<nexists>finextension s''. validfinpath M s' (finextension) s'' \<and> P s'')"
proof-
  have "enabledactions M s \<noteq> {}"
  proof
    assume "enabledactions M s = {}"
    hence "P s" using assms(1) by simp
    hence "validfinpath M s [] s \<and> P s" by simp
    thus "False" using assms(2) by blast
  qed
  from this obtain a s' where res1 : "(s, a, s') \<in> transition M" using actionenabled by metis
  let ?t = "(s, a, s')"
  have "(\<nexists>finextension s''. validfinpath M s' (finextension) s'' \<and> P s'')"
  proof
    assume "(\<exists>finextension s''. validfinpath M s' (finextension) s'' \<and> P s'')"
    from this obtain finextension s'' where "validfinpath M s' (finextension) s'' \<and> P s''" by auto
    hence "validfinpath M s (?t # finextension) s'' \<and> P s''" using res1 by simp
    thus "False" using assms(2) by blast
  qed
  thus "\<exists>a s'. (s, a, s') \<in> transition M \<and> (\<nexists>finextension s''. validfinpath M s' finextension s'' \<and> P s'')" using res1 by auto
qed

fun recursivepath :: "('s \<Rightarrow> 's \<times> 'a \<times> 's) \<Rightarrow> 's \<Rightarrow> nat \<Rightarrow> 's \<times> 'a \<times> 's" where
"recursivepath succ s 0 = succ s" | 
"recursivepath succ s (Suc n) = succ (target (recursivepath succ s n))"

lemma successorlemma : 
  assumes "(s \<in> S' \<and> (\<forall>s'. s' \<in> S' \<longrightarrow> (\<exists>t. source t = s' \<and> P t \<and> t \<in> transition M \<and> target t \<in> S')))"
  shows "(\<exists> p. validinfpath M s p \<and> (\<forall>n. P (p n)))"
  apply (simp add : validinfpath_def)
proof-
  from assms have "(\<exists> succ.(\<forall>s'. s' \<in> S' \<longrightarrow> (source (succ s') = s' \<and> succ s' \<in> transition M \<and> P (succ s') \<and> target (succ s') \<in> S')))" by metis
  from this obtain succ where assum1 : "\<forall>s'. s' \<in> S' \<longrightarrow> (source (succ s') = s' \<and> succ s' \<in> transition M \<and> P (succ s') \<and> target (succ s') \<in> S')" by auto
  let ?p = "recursivepath succ s"
  have "source (?p 0) = s" using assum1 assms by simp
  moreover have "(\<forall>n. target(?p n) \<in> S' \<and> ?p n \<in> transition M \<and> target (?p n) = source (?p (Suc n)) \<and> P (?p n))"
  proof
    fix n
    show "target(?p n) \<in> S' \<and> ?p n \<in> transition M \<and> target (?p n) = source (?p (Suc n)) \<and> P (?p n)"
      apply (induct n)
      using assum1 assms apply (simp)
    proof-
      fix n
      assume "target (recursivepath succ s n) \<in> S' \<and> recursivepath succ s n \<in> transition M \<and> target (recursivepath succ s n) = source (recursivepath succ s (Suc n)) \<and> P (recursivepath succ s n)"
      thus "target (recursivepath succ s (Suc n)) \<in> S' \<and> recursivepath succ s (Suc n) \<in> transition M \<and> target (recursivepath succ s (Suc n)) = source (recursivepath succ s (Suc (Suc n))) \<and> P (recursivepath succ s (Suc n))" using assum1 by auto
    qed
  qed
  ultimately have "s = source (?p 0) \<and> (\<forall>n. ?p n \<in> transition M \<and> target (?p n) = source (?p (Suc n))) \<and> (\<forall>n. P (?p n))" by auto
  thus "\<exists>p. s = source (p 0) \<and> (\<forall>n. p n \<in> transition M \<and> target (p n) = source (p (Suc n))) \<and> (\<forall>n. P (p n))" by blast
qed 

lemma successorlemma_no_pred : 
  assumes "s \<in> S' \<and> (\<forall>s'. s' \<in> S' \<longrightarrow> (\<exists>t. source t = s' \<and> t \<in> transition M \<and> target t \<in> S'))"
  shows "\<exists> p. validinfpath M s p"
proof-
  from assms have assum1: "(s \<in> S' \<and> (\<forall>s'. s' \<in> S' \<longrightarrow> (\<exists>t. source t = s' \<and> True \<and> t \<in> transition M \<and> target t \<in> S')))" by auto
  have "(\<exists> p. validinfpath M s p \<and> (\<forall>n. (\<lambda>t. True) (p n)))"
    apply (rule successorlemma)
    using assum1 apply (auto)
    done
  thus "(\<exists> p. validinfpath M s p)" by auto
qed

lemma extensionpath :
  assumes "\<forall>s. ((enabledactions M s = {}) \<longrightarrow> P s)"
  shows "(\<exists>finextension s''. validfinpath M s' finextension s'' \<and> P s'') \<or> (\<exists>infextension. validinfpath M s' infextension)"
proof-
  have "(\<nexists>finextension s''. validfinpath M s' finextension s'' \<and> P s'') \<Longrightarrow> (\<exists>infextension. validinfpath M s' infextension)"
  proof-
    assume assum1: "\<nexists>finextension s''. validfinpath M s' finextension s'' \<and> P s''"
    let ?S' = "{s. \<nexists>finextension s''. validfinpath M s (finextension) s'' \<and> P s''}"
    have res1: "s' \<in> ?S'" using assum1 by auto
    have res2: "\<forall>s'. s' \<in> ?S' \<longrightarrow> (\<exists>t. source t = s' \<and> t \<in> transition M \<and> target t \<in> ?S')" using assms assum1 invariantextension by auto
    show "\<exists> infextension. validinfpath M s' infextension"
      apply (rule successorlemma_no_pred)
      using res1 res2 apply blast
      done
  qed
  thus ?thesis by auto
qed  

lemma extendpath :
  assumes "\<forall>s. (enabledactions M s = {}) \<longrightarrow> P s"
  and "validfinpath M s p s'"
  shows "(\<exists>finextension s''. validfinpath M s (p @ finextension) s'' \<and> P s'') \<or> (\<exists>infextension. validinfpath M s (conc p infextension))"
proof-
  have "(\<exists>finextension s''. validfinpath M s' finextension s'' \<and> P s'') \<or> (\<exists>infextension. validinfpath M s' infextension)" using extensionpath assms(1) by metis 
  thus ?thesis using validinfpathsplit validfinpathsplit assms(2) by metis
qed

lemma splitvalidfinpathnotoccurslockedenabled : "(\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> (\<exists>s'' a. a \<in> \<alpha>\<^sub>e \<and> (s', a, s'' ) \<in> transition M)))
= ((\<exists>p' s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s') \<or> 
  (\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i < length p'. \<not>(occurs \<alpha>\<^sub>f (fin (take i p'))) \<and> action (p'!i) \<in> \<alpha>\<^sub>e) \<and> locked M B s') \<or>
  (\<exists>p'. validinfpath M s p' \<and>  (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and> action (p' i) \<in> \<alpha>\<^sub>e)))" 
  apply (rule iffI)
proof-
  assume "((\<exists>p' s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s') \<or> 
  (\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i < length p'. \<not>(occurs \<alpha>\<^sub>f (fin (take i p'))) \<and> action (p'!i) \<in> \<alpha>\<^sub>e) \<and> locked M B s') \<or>
  (\<exists>p'. validinfpath M s p' \<and>  (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and> action (p' i) \<in> \<alpha>\<^sub>e)))"
  moreover {
    assume "\<exists>p' s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s'"
    hence "\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> (\<exists>s'' a. a \<in> \<alpha>\<^sub>e \<and> (s', a, s'') \<in> transition M))" by auto
  }
  moreover {
    assume "\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i < length p'. \<not>(occurs \<alpha>\<^sub>f (fin (take i p'))) \<and> action (p'!i) \<in> \<alpha>\<^sub>e) \<and> locked M B s'"
    from this obtain p' s' i where assum1 : "i < length p' \<and> validfinpath M s p' s' \<and> \<not>(occurs \<alpha>\<^sub>f (fin (take i p'))) \<and> action (p'!i) \<in> \<alpha>\<^sub>e \<and> locked M B s'" by auto
    have "action (p'!i) \<in> \<alpha>\<^sub>e \<and> (source (p'!i), action (p'!i), target (p'!i)) \<in> transition M" using assum1 by auto
    hence "\<exists>s'' a. a \<in> \<alpha>\<^sub>e \<and> (source (p'!i), a, s'') \<in> transition M" by blast
    moreover have "validfinpath M s (take i p') (source (p'!i)) \<and> \<not>(occurs \<alpha>\<^sub>f (fin (take i p')))" using assum1 by auto
    ultimately have "\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (\<exists>s'' a. a \<in> \<alpha>\<^sub>e \<and> (s', a, s'') \<in> transition M)" by auto   
  }
  moreover {
    assume "\<exists>p'. validinfpath M s p' \<and>  (\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and> action (p' i) \<in> \<alpha>\<^sub>e)"
    from this obtain p' i where assum1 : "validinfpath M s p' \<and>  \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and>  action (p' i) \<in> \<alpha>\<^sub>e" by auto
    hence "p' i \<in> transition M \<and> action (p' i) \<in> \<alpha>\<^sub>e" using validinfpath_def by metis
    hence "(source (p' i), action (p' i), target (p' i)) \<in> transition M \<and> action (p' i) \<in> \<alpha>\<^sub>e" by simp
    hence "validfinpath M s (prefix i p') (source (p' i)) \<and> \<not>(occurs \<alpha>\<^sub>f (fin (prefix i p'))) \<and> (source (p' i), action (p' i), target (p' i)) \<in> transition M \<and> action (p' i) \<in> \<alpha>\<^sub>e" using assum1 validinfsubpath assum1 by metis
    hence "\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (\<exists>s'' a. a \<in> \<alpha>\<^sub>e \<and> (s', a, s'') \<in> transition M)" by blast
  }
  ultimately show "\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> (\<exists>s'' a. a \<in> \<alpha>\<^sub>e \<and> (s', a, s'' ) \<in> transition M))" by blast
next
  assume "\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> (\<exists>s'' a. a \<in> \<alpha>\<^sub>e \<and> (s', a, s'') \<in> transition M))"
  from this obtain p s' where "validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> (\<exists>s'' a. a \<in> \<alpha>\<^sub>e \<and> (s', a, s'') \<in> transition M))" by auto
  hence "(validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s') \<or> (validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (\<exists>s'' a. a \<in> \<alpha>\<^sub>e \<and> (s', a, s'') \<in> transition M))" by auto
  moreover {
    assume "(validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> locked M B s')"
    hence "(\<exists>p' s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s')" by auto
  }
  moreover {
    assume "(validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (\<exists>s'' a. a \<in> \<alpha>\<^sub>e \<and> (s', a, s'') \<in> transition M))"
    from this obtain s'' a where assum1 : "validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> a \<in> \<alpha>\<^sub>e \<and> (s', a, s'') \<in> transition M" by auto
    let ?t = "(s', a, s'')"
    have "validfinpath M s p s' \<and> validfinpath M s' [?t] s''" using assum1 by auto
    hence "validfinpath M s (p@[?t]) s''" using validfinpathsplit by metis
    moreover have "\<forall>s. (enabledactions M s = {}) \<longrightarrow> locked M B s" by (simp add: locked_def)
    ultimately have "(\<exists>finextension s''. validfinpath M s ((p@[?t]) @ finextension) s'' \<and> locked M B s'') \<or> (\<exists>infextension. validinfpath M s (conc (p@[?t]) infextension))" using extendpath by metis
    moreover {
      assume "\<exists>finextension s''. validfinpath M s ((p@[?t]) @ finextension) s'' \<and> locked M B s''"
      from this obtain finextension s'' where "validfinpath M s ((p@[?t]) @ finextension) s'' \<and> locked M B s''" by auto
      hence "validfinpath M s ((p@[?t]) @ finextension) s'' \<and> length p < length ((p@[?t]) @ finextension) \<and> \<not> occurs \<alpha>\<^sub>f (fin (take (length p) ((p@[?t]) @ finextension))) \<and> action (((p@[?t]) @ finextension) ! (length p)) \<in> \<alpha>\<^sub>e \<and> locked M B s''" using assum1 by auto
      hence "\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i < length p'. \<not> occurs \<alpha>\<^sub>f (fin (take i p')) \<and> action (p' ! i) \<in> \<alpha>\<^sub>e) \<and> locked M B s'" by metis
    }
    moreover {
      assume "\<exists>infextension. validinfpath M s (conc (p@[?t]) infextension)"
      from this obtain infextension where "validinfpath M s (conc (p@[?t]) infextension)" by auto
      moreover have "prefix (length p) (conc (p@[?t]) infextension) = p" by (induct p; simp)
      moreover have "(conc (p@[?t]) infextension) (length p) = ?t" by (induct p; simp)
      ultimately have "validinfpath M s (conc (p@[?t]) infextension) \<and> \<not> occurs \<alpha>\<^sub>f (fin (prefix (length p) (conc (p@[?t]) infextension))) \<and> action ((conc (p@[?t]) infextension) (length p)) \<in> \<alpha>\<^sub>e" using assum1 by auto
      hence "(\<exists>p'. validinfpath M s p' \<and> (\<exists>i. \<not> occurs \<alpha>\<^sub>f (fin (prefix i p')) \<and> action (p' i) \<in> \<alpha>\<^sub>e))" by blast
    }
    ultimately have "(\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i < length p'. \<not> occurs \<alpha>\<^sub>f (fin (take i p')) \<and> action (p' ! i) \<in> \<alpha>\<^sub>e) \<and> locked M B s')
      \<or> (\<exists>p'. validinfpath M s p' \<and> (\<exists>i. \<not> occurs \<alpha>\<^sub>f (fin (prefix i p')) \<and> action (p' i) \<in> \<alpha>\<^sub>e))" by auto
  }
  ultimately show "(\<exists>p' s'. validfinpath M s p' s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p') \<and> locked M B s') 
  \<or> (\<exists>p' s'. validfinpath M s p' s' \<and> (\<exists>i < length p'. \<not> occurs \<alpha>\<^sub>f (fin (take i p')) \<and> action (p' ! i) \<in> \<alpha>\<^sub>e) \<and> locked M B s') 
  \<or> (\<exists>p'. validinfpath M s p' \<and> (\<exists>i. \<not> occurs \<alpha>\<^sub>f (fin (prefix i p')) \<and> action (p' i) \<in> \<alpha>\<^sub>e))" by auto
qed

lemma splitcases : "(\<exists> p. freeuntiloccurrence p \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p) = ((\<exists>p s'. validfinpath M s p s' \<and> \<not> occurs \<alpha>\<^sub>f (fin p) \<and> (locked M B s' \<or> (\<exists>s'' a. a \<in> \<alpha>\<^sub>e \<and> (s', a, s'' ) \<in> transition M)))
  \<or> (\<exists>p. validinfpath M s p \<and> \<not> occurs \<alpha>\<^sub>f (inf p)))"
  apply (subst unfoldcases)
  apply (subst splitvalidfinpathnotoccurslockedenabled)
  apply (auto)
  done

lemma progressingsubpath : "progressing M s B p \<Longrightarrow> (\<exists>s'. validfinpath M s (pref i p) s' \<and> progressing M s' B (suff i p))"
  apply (cases p; simp)
  apply (metis append_take_drop_id validfinpathsplit)
  done

lemma splitviolating [simp] : "(\<exists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p) =
  (\<exists>p p' s'. match \<rho> p  \<and> validfinpath M s p s' \<and> freeuntiloccurrence p' \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s' B p')"
proof
  assume "\<exists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p"
  from this obtain p i where "match \<rho> (pref i p) \<and> freeuntiloccurrence (suff i p) \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p" by auto
  hence "\<exists>s'. match \<rho> (pref i p) \<and> validfinpath M s (pref i p) s' \<and> freeuntiloccurrence (suff i p) \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s' B (suff i p)"  by (metis progressingsubpath)
  thus "\<exists>p p' s'. match \<rho> p \<and> validfinpath M s p s' \<and> freeuntiloccurrence p' \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s' B p'" by auto
next
  assume "\<exists>p p' s'. match \<rho> p  \<and> validfinpath M s p s' \<and> freeuntiloccurrence p' \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s' B p'"
  from this obtain p p' s' where assum1: "match \<rho> p  \<and> validfinpath M s p s' \<and> freeuntiloccurrence p' \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s' B p'" by auto
  show "\<exists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p"
    apply (cases p')
  proof-
    fix finpath
    assume assum2 : "p' = fin finpath"
    have "match \<rho> p \<and> freeuntiloccurrence (fin finpath) \<alpha>\<^sub>f \<alpha>\<^sub>e" using assum1 assum2 by auto
    hence "match \<rho> (pref (length p) (fin (p@finpath))) \<and> freeuntiloccurrence ((suff (length p) (fin (p@finpath)))) \<alpha>\<^sub>f \<alpha>\<^sub>e" by auto
    hence res1 : "violating (fin (p@finpath)) \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e" unfolding violating.simps by metis
    have "validfinpath M s p s' \<and> (\<exists>s''. validfinpath M s' finpath s'' \<and> locked M B s'')" using assum1 assum2 by auto
    hence "\<exists>s''. validfinpath M s (p @ finpath) s'' \<and> locked M B s''" using validfinpathsplit by metis
    hence "progressing M s B (fin (p@finpath))" by auto
    thus "\<exists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p" using res1 by blast
  next
    fix infpath
    assume assum2 : "p' = inf infpath"
    have "match \<rho> p \<and> freeuntiloccurrence (inf infpath) \<alpha>\<^sub>f \<alpha>\<^sub>e" using assum1 assum2 by auto
    moreover have "prefix (length p) (conc p infpath) = p" by (induction p; simp)
    ultimately have "match \<rho> (prefix (length p) (conc p infpath)) \<and> freeuntiloccurrence (inf (suffix (length p) (conc p infpath))) \<alpha>\<^sub>f \<alpha>\<^sub>e" by auto
    hence res1: "violating (inf (conc p infpath)) \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e" unfolding violating.simps pref.simps suff.simps by blast
    have "validfinpath M s p s' \<and> validinfpath M s' infpath" using assum1 assum2 by auto
    hence "validinfpath M s (conc p infpath)" using validinfpathsplit by metis
    hence "progressing M s B (inf (conc p infpath))" by auto
    thus "\<exists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p" using res1 by blast
qed
qed

lemma suffpredicate: 
  assumes "\<forall>p s. (\<exists>s'. validfinpath M s p s' \<and> P s (fin p)) = progressing M s B (fin p)"
  and "\<forall>p s. validinfpath M s p \<longrightarrow> (P s (inf p) = (\<exists>a \<in> -B. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (\<exists>j\<ge>i. action (p j) \<in> \<alpha>_el a \<or> target (p j) \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) ))))"  
  shows "validfinpath M s (pref i p) s' \<and> progressing M s' B (suff i p) \<and> P s p \<longrightarrow> P s' (suff i p)"
  apply (cases p)
proof
  fix finpath
  assume assum1: "p = fin finpath"
  assume "validfinpath M s (pref i p) s' \<and> progressing M s' B (suff i p) \<and> P s p"
  hence "validfinpath M s (take i finpath) s' \<and> (\<exists>s''. validfinpath M s' (drop i finpath) s'' \<and> locked M B s'') \<and> P s (fin finpath)" using assum1 by simp
  hence "progressing M s' B (fin (drop i finpath))" by simp
  thus "P s' (suff i p)" using assum1 assms(1) by auto
next
  fix infpath
  assume assum1: "p = inf infpath"
  show "validfinpath M s (pref i p) s' \<and> progressing M s' B (suff i p) \<and> P s p \<longrightarrow> P s' (suff i p)"
  proof
    assume "validfinpath M s (pref i p) s' \<and> progressing M s' B (suff i p) \<and> P s p"
    hence assum2: "validfinpath M s (prefix i infpath) s' \<and> validinfpath M s' (suffix i infpath) \<and> P s (inf infpath)" using assum1 by simp
    moreover have "conc (prefix i infpath) (suffix i infpath) = infpath" by simp
    ultimately have "validinfpath M s infpath \<and> P s (inf infpath)" using validinfpathsplit by metis
    from this obtain a where assum3: "a \<in> -B \<and> ((\<forall>l. (source (infpath l)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (\<exists>j\<ge>l. action (infpath j) \<in> \<alpha>_el a \<or> target (infpath j) \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e)))" using assms(2) by auto
    have "((\<forall>l. (source ((suffix i infpath) l)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (\<exists>j\<ge>l. action ((suffix i infpath) j) \<in> \<alpha>_el a \<or> target ((suffix i infpath) j) \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e)))"
    proof
      fix l
      show "source (suffix i infpath l) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (\<exists>j\<ge>l. action (suffix i infpath j) \<in> \<alpha>_el a \<or> target (suffix i infpath j) \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e)"
      proof
        assume "source (suffix i infpath l) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e"
        hence "source (infpath (i + l)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e" by simp
        from this obtain j where "j \<ge> (i + l) \<and>  (action (infpath j) \<in> \<alpha>_el a \<or> target (infpath j) \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e)" using assum3 by auto
        hence "(j - i) \<ge> l \<and>  (action ((suffix i infpath) (j - i)) \<in> \<alpha>_el a \<or> target ((suffix i infpath) (j - i)) \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e)" by auto
        thus "(\<exists>j\<ge>l. action (suffix i infpath j) \<in> \<alpha>_el a \<or> target (suffix i infpath j) \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e)" by auto
      qed
    qed
    hence "a \<in> -B \<and> ((\<forall>l. (source ((suffix i infpath) l)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (\<exists>j\<ge>l. action ((suffix i infpath) j) \<in> \<alpha>_el a \<or> target ((suffix i infpath) j) \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e)))" using assum3 by auto
    hence "P s' (inf (suffix i infpath))" using assms(2) assum2 by auto
    thus "P s' (suff i p)" using assum1 by auto
  qed
qed

lemma splitviolating' [simp] : 
  assumes "\<forall>p s. (\<exists>s'. validfinpath M s p s' \<and> P s (fin p)) = progressing M s B (fin p)"
  and "\<forall>p s. validinfpath M s p \<longrightarrow> (P s (inf p) = (\<exists>a \<in> -B. ((\<forall>i. (source (p i)) \<in> \<lbrakk>shiftdown (\<phi>_on a) 0\<rbrakk> M e \<longrightarrow> (\<exists>j\<ge>i. action (p j) \<in> \<alpha>_el a \<or> target (p j) \<in> \<lbrakk>shiftdown (\<phi>_off a) 0\<rbrakk> M e) ))))"  
  shows "(\<exists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p \<and> P s p) = 
  (\<exists>p p' s'. match \<rho> p  \<and> validfinpath M s p s' \<and> freeuntiloccurrence p' \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s' B p' \<and> P s' p')"
proof
  assume "\<exists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p \<and> P s p"
  from this obtain p i where assum1: "match \<rho> (pref i p) \<and> freeuntiloccurrence (suff i p) \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p \<and> P s p" by auto
  hence "\<exists>s'. match \<rho> (pref i p) \<and> validfinpath M s (pref i p) s' \<and> freeuntiloccurrence (suff i p) \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s' B (suff i p) \<and> P s p" by (metis progressingsubpath)
  from this obtain s' where res1: "match \<rho> (pref i p) \<and> validfinpath M s (pref i p) s' \<and> freeuntiloccurrence (suff i p) \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s' B (suff i p) \<and> P s p" by auto
  hence "validfinpath M s (pref i p) s' \<and> progressing M s' B (suff i p) \<and> P s p" by simp
  hence "P s' (suff i p)" 
    apply (subst suffpredicate [where ?M="M" and ?B="B" and ?\<phi>_on="\<phi>_on" and ?\<phi>_off="\<phi>_off" and ?\<alpha>_el="\<alpha>_el"and ?e="e" and ?s="s"])
    apply (metis assms(1))
    apply (metis assms(2))
    apply simp
    apply simp
    done
  thus "\<exists>p p' s'. match \<rho> p \<and> validfinpath M s p s' \<and> freeuntiloccurrence p' \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s' B p' \<and> P s' p'" using res1 by auto
next
  assume "\<exists>p p' s'. match \<rho> p  \<and> validfinpath M s p s' \<and> freeuntiloccurrence p' \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s' B p' \<and> P s' p'"
  from this obtain p p' s' where assum1: "match \<rho> p  \<and> validfinpath M s p s' \<and> freeuntiloccurrence p' \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s' B p' \<and> P s' p'" by auto
  show "\<exists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p \<and> P s p"
    apply (cases p')
  proof-
    fix finpath
    assume assum2 : "p' = fin finpath"
    have "match \<rho> p \<and> freeuntiloccurrence (fin finpath) \<alpha>\<^sub>f \<alpha>\<^sub>e" using assum1 assum2 by auto
    hence "match \<rho> (pref (length p) (fin (p@finpath))) \<and> freeuntiloccurrence ((suff (length p) (fin (p@finpath)))) \<alpha>\<^sub>f \<alpha>\<^sub>e" by auto
    hence res1 : "violating (fin (p@finpath)) \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e" unfolding violating.simps by metis
    have "validfinpath M s p s' \<and> (\<exists>s''. validfinpath M s' finpath s'' \<and> locked M B s'')" using assum1 assum2 by auto
    hence "\<exists>s''. validfinpath M s (p @ finpath) s'' \<and> locked M B s''" using validfinpathsplit by metis
    hence res2: "progressing M s B (fin (p@finpath))" by auto
    hence "P s (fin (p@finpath))" using assms(1) by metis
    thus "\<exists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p \<and> P s p" using res1 res2 by blast
  next
    fix infpath
    assume assum2 : "p' = inf infpath"
    have "match \<rho> p \<and> freeuntiloccurrence (inf infpath) \<alpha>\<^sub>f \<alpha>\<^sub>e" using assum1 assum2 by auto
    moreover have "prefix (length p) (conc p infpath) = p" by (induction p; simp)
    ultimately have "match \<rho> (prefix (length p) (conc p infpath)) \<and> freeuntiloccurrence (inf (suffix (length p) (conc p infpath))) \<alpha>\<^sub>f \<alpha>\<^sub>e" by auto
    hence res1: "violating (inf (conc p infpath)) \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e" unfolding violating.simps pref.simps suff.simps by metis
    have "validfinpath M s p s' \<and> validinfpath M s' infpath" using assum1 assum2 by simp
    hence "validinfpath M s (conc p infpath)" using validinfpathsplit by metis
    hence res2: "progressing M s B (inf (conc p infpath))" by auto
        (*persistent property has not yet been formalized*)
    hence "P s (inf (conc p infpath))" by sorry
    thus "\<exists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p \<and> P s p" using res1 res2 by blast
qed
qed

end