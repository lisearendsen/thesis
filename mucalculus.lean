import Mathlib.Data.Set.Basic
open Set

inductive formula {Act : Type} where
| tt : formula
| ff : formula
| var : ℕ → formula
| neg : formula → formula
| and : formula → formula → formula
| or : formula → formula → formula
| box : Act → formula → formula
| diamond : Act → formula → formula
| nu : formula → formula
| mu : formula → formula

open formula

def negvari {Act : Type} (f : @formula Act) (i : ℕ) : @formula Act :=
match f with
| tt => tt
| ff => ff
| var X => if (X = i) then (neg (var X)) else (var X)
| neg f => neg (negvari f i)
| .and f f' => and (negvari f i) (negvari f' i)
| .or f f' => or (negvari f i) (negvari f' i)
| diamond act f => diamond act (negvari f i)
| box act f => box act (negvari f i)
| nu f => nu (negvari f (Nat.succ i))
| mu f => mu (negvari f (Nat.succ i))

structure lts {Act : Type} where
 makelts :: (State : Type)
            (transition : Set (State × Act × State))
            (initial : Set (State))

def newenvironment {Act : Type} {M : @lts Act} (e : ℕ → Set M.State) (S : Set M.State) (n : ℕ) : Set M.State:=
    match n with
    | Nat.zero => S
    | Nat.succ n' => e n'

def formulasemantics {Act : Type} (form : @formula Act) (M : @lts Act) (e : ℕ → Set M.State) : Set (M.State):=
  match form with
  | tt => univ
  | ff => ∅
  | var X => e X
  | neg f => (formulasemantics f M e)ᶜ
  | .and f f' => (formulasemantics f M e) ∩ (formulasemantics f' M e)
  | .or f f' => (formulasemantics f M e) ∪ (formulasemantics f' M e)
  | box act f => {s : M.State | ∀ s' : M.State, (s, act, s') ∈ M.transition → s' ∈ (formulasemantics f M e)}
  | diamond act f => {s : M.State | ∃ s' : M.State, (s, act, s') ∈ M.transition ∧ s' ∈ (formulasemantics f M e)}
  | nu f => {s : M.State | ∃ S' : Set M.State, S' ⊆ (formulasemantics f M (newenvironment e S')) ∧ s ∈ S'}
  | mu f => {s : M.State | ∀ S' : Set M.State, (formulasemantics f M (newenvironment e S')) ⊆ S' → s ∈ S'}

def validactionpath {Act : Type} (M : @lts Act) (p : Nat → M.State) (act : Act) : Prop :=
∀ n : ℕ, (p n, act, p (Nat.succ n)) ∈ M.transition

lemma nuX_X (Act : Type) (M : @lts Act) (e : ℕ → Set M.State) :
(formulasemantics (formula.nu (formula.var 0)) M e) = univ := by
apply Subset.antisymm
intro x h1
apply mem_univ
intro x h1
unfold formulasemantics formulasemantics newenvironment
use univ

lemma nuX_diamondactXrtl (Act : Type) (M : @lts Act) (e : ℕ → Set M.State) (act : Act) (s : M.State):
(∃ p, validactionpath M p act ∧ p 0 = s) →
    (s ∈ formulasemantics (nu (diamond act (var 0))) M e)
:= by
simp!
unfold validactionpath
intro p h1 h2
use {s' | ∃ n, p n = s'}
simp!
apply And.intro
intro n
use p (Nat.succ n)
apply And.intro
exact h1 n
simp!
use 0

def succesorpath {Act : Type} {M : @lts Act} (succ : M.State → M.State) (s : M.State) (n : ℕ) : M.State :=
match n with
| Nat.zero => s
| Nat.succ n' => succ (succesorpath succ s n')

lemma sucessorlemma1 (Act : Type) (M : @lts Act) (act : Act) (s : M.State):
(∃ S' : Set M.State, s ∈ S' ∧ ∀ s' : M.State, ∃ succ : M.State , s' ∈ S' → ((s', act, succ) ∈ M.transition ∧ succ ∈ S'))
    → (∃ S' : Set M.State, s ∈ S' ∧ ∃ succ : M.State → M.State, ∀ s' : M.State, s' ∈ S' → ((s', act, succ s') ∈ M.transition ∧ succ s' ∈ S'))
    := by
intro h1
rcases h1 with ⟨S', h1, h2⟩
use S'
apply And.intro
exact h1
have h3 : ∀ (s' : M.State), ∃ succ, s' ∉ S' ∨ (s', act, succ) ∈ M.transition ∧ succ ∈ S' := by
    intro s'
    have h2 := h2 s'
    rcases h2 with ⟨succ, h2⟩
    use succ
    by_cases h4 : s' ∈ S'
    right
    exact h2 h4
    left
    exact h4
use (fun s' => Classical.choose (h3 s'))
intro s' h4
have h3 := Classical.choose_spec (h3 s')
rcases h3 with h3left | h3right
exact False.elim (h3left h4)
exact h3right

lemma sucessorlemma2 (Act : Type) (M : @lts Act) (act : Act) (s : M.State):
(∃ S' : Set M.State, s ∈ S' ∧ ∃ succ : M.State → M.State, ∀ s' : M.State, s' ∈ S' → ((s', act, succ s') ∈ M.transition ∧ succ s' ∈ S'))
    → (∃ p, validactionpath M p act ∧ p 0 = s) := by
intro h1
rcases h1 with ⟨S, h1, succ, h2⟩
unfold validactionpath
use succesorpath succ s
apply And.intro
simp!
have h3 : ∀ (n : ℕ), (succesorpath succ s n, act, succ (succesorpath succ s n)) ∈ M.transition ∧ succ (succesorpath succ s n) ∈ S:= by
    intro n
    induction n
    case zero =>
        unfold succesorpath
        exact (h2 s h1)
    case succ n ih =>
        unfold succesorpath
        apply (h2 (succ (succesorpath succ s n)) ih.right)
intro n
exact (h3 n).left
unfold succesorpath
rfl

lemma nuX_diamondactX (Act : Type) (M : @lts Act) (e : ℕ → Set M.State) (act : Act) (s : M.State):
(s ∈ formulasemantics (nu (diamond act (var 0))) M e)
    ↔ (∃ p, validactionpath M p act ∧ p 0 = s) := by
apply Iff.intro
simp!
intro S' h1 h2
apply sucessorlemma2
apply sucessorlemma1
use S'
apply And.intro
exact h2
intro s'
by_cases h4 : s' ∈ S'
have h5 : ∃ s'', (s', act, s'') ∈ M.transition ∧ s'' ∈ S' := h1 h4
rcases h5 with ⟨succ, h5⟩
use succ
intro h6
exact h5
use s
intro h6
by_contra
exact h4 h6
apply nuX_diamondactXrtl

#print axioms nuX_diamondactX
#print propext
#print Quot.sound
#print Classical.choice
#print axioms Classical.em

lemma neg_eq_newenv (Act : Type) (M : @lts Act)
(f : @formula Act):
∀ i : ℕ, ∀ e : ℕ → Set M.State,
    formulasemantics (negvari f i) M e =
    formulasemantics f M (fun n => (if (n = i) then (e n)ᶜ else (e n)))
    := by
induction f with
| tt | ff | neg f ih =>
    simp!
    try exact ih
| var X =>
    intro i e
    unfold negvari
    split_ifs with h2
    unfold formulasemantics
    rewrite [h2]
    simp!
    unfold formulasemantics
    simp [h2]
| and f f' ihf ihf' | or f f' ihf ihf'
| diamond act f ihf | box act f ihf  =>
    intro i e
    simp!
    rewrite [ihf]
    try rewrite [ihf']
    rfl
| nu f ihf | mu f ihf  =>
    intro i e
    simp!
    have h1 : ∀ S' : Set M.State, formulasemantics (negvari f (i + 1)) M (newenvironment e S') =
        formulasemantics f M (newenvironment (fun n ↦ if n = i then (e n)ᶜ else e n) S') := by
        intro S'
        rewrite [ihf]
        have h2 : (fun n ↦ if n = i + 1 then (newenvironment e S' n)ᶜ else newenvironment e S' n)
            = (newenvironment (fun n ↦ if n = i then (e n)ᶜ else e n) S') := by
            funext n
            cases n with
            | zero => simp!
            | succ n' =>
                by_cases h3 : (n' = i)
                simp!
                simp!
        rewrite [h2]
        rfl
    apply Subset.antisymm
    intro x h2
    rewrite [mem_setOf]
    rewrite [mem_setOf] at h2
    try intro S'
    try have h2 := h2 S'
    try rcases h2 with ⟨S', h2⟩
    try exists S'
    rewrite [h1] at h2
    exact h2
    intro x h2
    rewrite [mem_setOf]
    rewrite [mem_setOf] at h2
    try intro S'
    try have h2 := h2 S'
    try rcases h2 with ⟨S', h2⟩
    try exists S'
    rewrite [h1]
    exact h2

lemma newenvironmentzero (Act : Type) (M : @lts Act) (S' : Set M.State)
(e : ℕ → Set M.State) :
(fun n ↦ if n = 0 then (newenvironment e S' n)ᶜ else (newenvironment e S' n))
    = (newenvironment e (S')ᶜ) := by
funext n
cases n with
    | zero => simp!
    | succ n' => simp!

lemma negnu (Act : Type) (M : @lts Act) (e : ℕ → Set M.State) (f : @formula Act) :
formulasemantics (neg (nu f)) M e
    = formulasemantics (mu (neg (negvari f 0))) M e := by
simp!
apply Subset.antisymm
intro x h1
rewrite [mem_setOf]
rewrite [mem_compl_iff] at h1
rewrite [mem_setOf] at h1
push_neg at h1
intro S' h2
rewrite [neg_eq_newenv, newenvironmentzero] at h2
have h1 := h1 (S')ᶜ
simp at h1
apply h1
rewrite [compl_subset_comm]
exact h2
intro x h1
rewrite [mem_setOf] at h1
rewrite [mem_compl_iff]
rewrite [mem_setOf]
push_neg
intro S' h2
have h1 := h1 (S')ᶜ
simp at h1
apply h1
rewrite [neg_eq_newenv, newenvironmentzero]
rewrite [compl_compl]
exact h2
