import ClassicalLogicLean.LN.Binders
import ClassicalLogicLean.LN.Semantics
import MathlibExtraLean.List
import MathlibExtraLean.FunctionUpdateITE


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


namespace LN

open Var Formula


-- Single

/--
  Helper function for openFormulaAux.

  v is intended to be a free variable.
-/
def openVar
  (k : ℕ)
  (v : Var) :
  Var → Var
  | free_ x => free_ x
  | bound_ i => if i = k then v else bound_ i


/--
  Helper function for openFormula.

  v is intended to be a free variable.
-/
def openFormulaAux
  (k : ℕ)
  (v : Var) :
  Formula → Formula
  | pred_ X vs => pred_ X (vs.map (openVar k v))
  | not_ phi => not_ (openFormulaAux k v phi)
  | imp_ phi psi => imp_ (openFormulaAux k v phi) (openFormulaAux k v psi)
  | forall_ x phi => forall_ x (openFormulaAux (k + 1) v phi)


/--
  openFormula v F := Each of the bound variables in the formula F that has an index equal to the number of binders that it is under is replaced by the variable v. This means that v replaces each bound variable that has an index out of scope by exactly one.

  v is intended to be a free variable.
-/
def openFormula
  (v : Var)
  (F : Formula) :
  Formula :=
  openFormulaAux 0 v F


-- Multiple

/--
  Helper function for openFormulaListAux.

  This is a multiple variable version of openVar.

  zs is intended to be an array of free variables.
-/
def openVarList
  (k : Nat)
  (zs : List Var) :
  Var → Var
  | free_ x => free_ x
  | bound_ i =>
    if i < k
    -- i is in scope
    then bound_ i
    else
    -- i is out of scope
      -- ¬ i < k -> i >= k -> i - k >= 0 -> 0 <= i - k
      if _ : i - k < zs.length
      -- 0 <= i - k < zs.length
      then zs[i - k]
      -- The index of each of the remaining out of scope bound variables is reduced to account for the zs.length number of out of scope indexes that have been removed.
      -- ¬ i - k < zs.length -> i - k >= zs.length -> i >= zs.length + k -> i - zs.length >= k. Since k >= 0 then i - zs.length >= 0.
      else bound_ (i - zs.length)


/--
  Helper function for openFormulaList.

  This is a multiple variable version of openFormulaAux.

  zs is intended to be an array of free variables.
-/
def openFormulaListAux
  (k : Nat)
  (zs : List Var) :
  Formula → Formula
  | pred_ X vs => pred_ X (vs.map (openVarList k zs))
  | not_ phi => not_ (openFormulaListAux k zs phi)
  | imp_ phi psi => imp_ (openFormulaListAux k zs phi) (openFormulaListAux k zs psi)
  | forall_ x phi => forall_ x (openFormulaListAux (k + 1) zs phi)


/--
  This is a multiple variable version of openFormula.

  Let zs be an array of variables. Let (bound_ i) be a bound variable in the formula F. Let k be the number of binders that an occurrence of (bound_ i) is under. Then that occurrence of (bound_ i) is changed according to:

  i < k : (bound_ i) -> (bound_ i)
  k <= i < k + zs.size : (bound_ i) -> zs[i - k]
  k + zs.size <= i : (bound_ i) -> bound_ (i - zs.size)

  zs is intended to be an array of free variables.
-/
def openFormulaList
  (zs : List Var)
  (F : Formula) :
  Formula :=
  openFormulaListAux 0 zs F


--------------------------------------------------


/-
def Var.instantiate1 (k : Nat) (v : Var) : Var → Var
  | free_ x => free_ x
  | bound_ i =>
      if i < k
      then bound_ i
      else
        if i = k
        then v
        else bound_ (i - 1)


def Var.instantiate
  (k : Nat) :
  List Var → (Var → Var)
  | [] => id
  | v :: vs => Var.instantiate k vs ∘ Var.instantiate1 k v
-/


def Var.instantiate
  (k : Nat)
  (zs : List Var) : Var → Var
  | free_ x => free_ x
  | bound_ i =>
      if i < k
      then bound_ i
      else
        let i := i - k
        if _ : i < zs.length
        then zs[i]
        else bound_ (i - zs.length + k)


def Formula.instantiate
  (k : Nat)
  (zs : List Var) :
  Formula → Formula
  | pred_ X vs => pred_ X (vs.map (Var.instantiate k zs))
  | not_ phi => not_ (Formula.instantiate k zs phi)
  | imp_ phi psi => imp_ (Formula.instantiate k zs phi) (Formula.instantiate k zs psi)
  | forall_ x phi => forall_ x (Formula.instantiate (k + 1) zs phi)


--------------------------------------------------


def Var.abstract1
  (v : Var)
  (k : ℕ) :
  Var → Var
  | free_ x =>
      if v = free_ x
      then bound_ k
      else free_ x
  | bound_ i =>
      if i < k
      then bound_ i
      else bound_ (i + 1)


--------------------------------------------------


/--
  Helper function for closeFormulaAux.

  v is intended to be a free variable.
-/
def closeVar
  (v : Var)
  (k : ℕ) :
  Var → Var
  | free_ x => if v = free_ x then bound_ k else free_ x
  | bound_ i => bound_ i


/--
  Helper function for closeFormula.

  v is intended to be a free variable.
-/
def closeFormulaAux
  (v : Var)
  (k : ℕ) :
  Formula → Formula
  | pred_ X vs => pred_ X (vs.map (closeVar v k))
  | not_ phi => not_ (closeFormulaAux v k phi)
  | imp_ phi psi => imp_ (closeFormulaAux v k phi) (closeFormulaAux v k psi)
  | forall_ x phi => forall_ x (closeFormulaAux v (k + 1) phi)


/--
  closeFormula v F := If v is a free variable then each occurence of v in the formula F is replaced by a bound variable that has an index equal to the number of binders that it is under. This means that each occurence of v is replaced by a bound variable that has an index out of scope by exactly one.

  v is intended to be a free variable.
-/
def closeFormula
  (v : Var)
  (F : Formula) :
  Formula :=
  closeFormulaAux v 0 F


--------------------------------------------------


/--
  Helper function for Formula.lc_at.
-/
def Var.lc_at
  (k : ℕ) :
  Var → Prop
  | free_ _ => True
  | bound_ i => i < k

instance
  (k : ℕ) (v : Var) :
  Decidable (Var.lc_at k v) :=
  by
  cases v
  all_goals
    simp only [lc_at]
    infer_instance


/--
  For k = 0 this is a recursive definition of locally closed.

  Formula.lc_at k F := True if and only if every bound variable in the formula F has an index less than the number of binders that it is under plus k. If this holds for k = 0 then this means that no bound variable in F is out of scope and hence that F is locally closed.
-/
def Formula.lc_at
  (k : ℕ) :
  Formula → Prop
  | pred_ _ vs => ∀ (v : Var), v ∈ vs → (v.lc_at k)
  | not_ phi => phi.lc_at k
  | imp_ phi psi => (phi.lc_at k) ∧ (psi.lc_at k)
  | forall_ _ phi => phi.lc_at (k + 1)

instance (k : ℕ) (F : Formula) : Decidable (Formula.lc_at k F) :=
  by
  induction F generalizing k
  all_goals
    unfold Formula.lc_at
    infer_instance


#eval Formula.lc_at 0 (pred_ "X" [free_ "x"])
#eval Formula.lc_at 0 (pred_ "X" [bound_ 0])
#eval Formula.lc_at 0 (forall_ "x" (pred_ "X" [bound_ 0]))
#eval Formula.lc_at 0 (forall_ "x" (pred_ "X" [bound_ 1]))


inductive Formula.lc : Formula → Prop
  | pred_
    (X : String)
    (vs : List Var) :
    (∀ (v : Var), v ∈ vs → v.isFree) →
    lc (pred_ X vs)

  | not_
    (phi : Formula) :
    lc phi →
    lc (not_ phi)

  | imp_
    (phi psi : Formula) :
    lc phi →
    lc psi →
    lc (imp_ phi psi)
/-
  | forall_
    (x : String)
    (phi : Formula)
    (L : Finset String) :
    (∀ (z : String), z ∉ L → lc (Formula.instantiate 0 [Var.free_ z] phi)) →
    lc (forall_ x phi)
-/
  | forall_
    (x : String)
    (phi : Formula)
    (z : String) :
    lc (Formula.instantiate 0 [Var.free_ z] phi) →
    lc (forall_ x phi)


--------------------------------------------------


def shift_list
  (D : Type)
  (V : VarAssignment D) : List D → VarAssignment D
  | [] => V
  | d :: ds => shift D (shift_list D V ds) d


def Formula.predSub
  (τ : String → ℕ → Formula) :
  Formula → Formula
  | pred_ X vs => Formula.instantiate 0 vs (τ X vs.length)
  | not_ phi => not_ (phi.predSub τ)
  | imp_ phi psi => imp_ (phi.predSub τ) (psi.predSub τ)
  | forall_ x phi => forall_ x (phi.predSub τ)


/-
def Interpretation.usingPred
  (D : Type)
  (I : Interpretation D)
  (pred_ : String → List D → Prop) :
  Interpretation D := {
    nonempty_ := I.nonempty_
    pred_ := pred_ }
-/


--------------------------------------------------


lemma CloseVarOpenVarComp
  (v : Var)
  (y : String)
  (k : ℕ)
  (h1 : ¬ free_ y = v) :
  (closeVar (free_ y) k ∘ openVar k (free_ y)) v = v :=
  by
  cases v
  case free_ x =>
    simp only [free_.injEq] at h1

    simp only [Function.comp_apply]
    simp only [openVar]
    simp only [closeVar]
    split
    case isTrue c1 =>
      simp only [free_.injEq] at c1
      contradiction
    case isFalse c2 =>
      apply Eq.refl
  case bound_ i =>
    simp only [Function.comp_apply]
    simp only [openVar]
    split
    case isTrue c1 =>
      rewrite [c1]

      simp only [closeVar]
      split
      case isTrue c2 =>
        apply Eq.refl
      case isFalse c2 =>
        contradiction
    case isFalse c1 =>
      simp only [closeVar]


lemma OpenVarCloseVarComp
  (v : Var)
  (k : ℕ)
  (y : String)
  (h1 : Var.lc_at k v) :
  (openVar k (free_ y) ∘ closeVar (free_ y) k) v = v :=
  by
  cases v
  case free_ x =>
    simp only [Function.comp_apply]
    simp only [closeVar]
    split
    case isTrue c1 =>
      rewrite [c1]
      simp only [openVar]
      split
      case isTrue c2 =>
        apply Eq.refl
      case isFalse c2 =>
        contradiction
    case isFalse c1 =>
      simp only [openVar]
  case bound_ i =>
    simp only [Var.lc_at] at h1

    simp only [Function.comp_apply]
    simp only [closeVar]
    simp only [openVar]
    split
    case isTrue c1 =>
      rewrite [c1] at h1
      simp only [lt_self_iff_false] at h1
    case isFalse c1 =>
      apply Eq.refl


lemma CloseFormulaOpenFormulaComp
  (F : Formula)
  (y : String)
  (k : ℕ)
  (h1 : ¬ occursIn (free_ y) F) :
  (closeFormulaAux (free_ y) k ∘ openFormulaAux k (free_ y)) F = F :=
  by
  induction F generalizing k
  case pred_ X vs =>
    simp only [occursIn] at h1

    simp only [Function.comp_apply]
    simp only [openFormulaAux]
    simp only [closeFormulaAux]
    simp only [List.map_map]
    congr
    simp only [List.map_eq_self_iff_fun_is_id_on_mem]
    intro v a1
    apply CloseVarOpenVarComp
    intro contra
    rewrite [← contra] at a1
    contradiction
  case not_ phi phi_ih =>
    simp only [occursIn] at h1

    simp only [Function.comp_apply] at phi_ih

    simp only [Function.comp_apply]
    simp only [openFormulaAux]
    simp only [closeFormulaAux]
    congr
    apply phi_ih
    exact h1
  case imp_ phi psi phi_ih psi_ih =>
    simp only [occursIn] at h1
    simp only [not_or] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    simp only [Function.comp_apply] at phi_ih

    simp only [Function.comp_apply]
    simp only [openFormulaAux]
    simp only [closeFormulaAux]
    congr
    · apply phi_ih
      exact h1_left
    · apply psi_ih
      exact h1_right
  case forall_ _ phi phi_ih =>
    simp only [occursIn] at h1

    simp only [Function.comp_apply] at phi_ih

    simp only [Function.comp_apply]
    simp only [openFormulaAux]
    simp only [closeFormulaAux]
    congr
    apply phi_ih
    exact h1


lemma OpenFormulaCloseFormulaComp
  (F : Formula)
  (k : ℕ)
  (y : String)
  (h1 : Formula.lc_at k F) :
  (openFormulaAux k (free_ y) ∘ closeFormulaAux (free_ y) k) F = F :=
  by
  induction F generalizing k
  case pred_ X vs =>
    simp only [Formula.lc_at] at h1

    simp only [Function.comp_apply]
    simp only [closeFormulaAux]
    simp only [openFormulaAux]
    simp only [List.map_map]
    congr
    simp only [List.map_eq_self_iff_fun_is_id_on_mem]
    intro v a1
    apply OpenVarCloseVarComp
    apply h1
    exact a1
  case not_ phi phi_ih =>
    simp only [Formula.lc_at] at h1

    simp only [Function.comp_apply] at phi_ih

    simp only [Function.comp_apply]
    simp only [closeFormulaAux]
    simp only [openFormulaAux]
    congr
    apply phi_ih
    exact h1
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.lc_at] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    simp only [Function.comp_apply] at phi_ih

    simp only [Function.comp_apply]
    simp only [closeFormulaAux]
    simp only [openFormulaAux]
    congr
    · apply phi_ih
      exact h1_left
    · apply psi_ih
      exact h1_right
  case forall_ _ phi phi_ih =>
    simp only [Formula.lc_at] at h1

    simp only [Function.comp_apply] at phi_ih

    simp only [Function.comp_apply]
    simp only [closeFormulaAux]
    simp only [openFormulaAux]
    congr
    apply phi_ih
    exact h1


--------------------------------------------------


lemma OpenVarLeftInvOn
  (k : ℕ)
  (y : String) :
  Set.LeftInvOn (closeVar (free_ y) k) (openVar k (free_ y)) {v : Var | ¬ (free_ y) = v} :=
  by
  simp only [Set.LeftInvOn]
  simp only [Set.mem_setOf_eq]
  intro v a1
  apply CloseVarOpenVarComp
  exact a1


lemma CloseVarLeftInvOn
  (y : String)
  (k : ℕ) :
  Set.LeftInvOn (openVar k (free_ y)) (closeVar (free_ y) k) {v : Var | Var.lc_at k v} :=
  by
  simp only [Set.LeftInvOn]
  simp only [Set.mem_setOf_eq]
  intro v a1
  apply OpenVarCloseVarComp
  exact a1


lemma OpenVarInjOn
  (k : ℕ)
  (y : String) :
  Set.InjOn (openVar k (free_ y)) {v : Var | ¬ (free_ y) = v} :=
  by
  apply Set.LeftInvOn.injOn
  apply OpenVarLeftInvOn


lemma CloseVarInjOn
  (y : String)
  (k : ℕ) :
  Set.InjOn (closeVar (free_ y) k) {v : Var | Var.lc_at k v} :=
  by
  apply Set.LeftInvOn.injOn
  apply CloseVarLeftInvOn


lemma OpenFormulaLeftInvOn
  (k : ℕ)
  (y : String) :
  Set.LeftInvOn (closeFormulaAux (free_ y) k) (openFormulaAux k (free_ y)) {F : Formula | ¬ occursIn (free_ y) F} :=
  by
  simp only [Set.LeftInvOn]
  simp only [Set.mem_setOf_eq]
  intro F a1
  apply CloseFormulaOpenFormulaComp
  exact a1


lemma CloseFormulaLeftInvOn
  (y : String)
  (k : ℕ) :
  Set.LeftInvOn (openFormulaAux k (free_ y)) (closeFormulaAux (free_ y) k) {F : Formula | Formula.lc_at k F} :=
  by
  simp only [Set.LeftInvOn]
  simp only [Set.mem_setOf_eq]
  intro F a1
  apply OpenFormulaCloseFormulaComp
  exact a1


lemma OpenFormulaInjOn
  (k : ℕ)
  (y : String) :
  Set.InjOn (openFormulaAux k (free_ y)) {F : Formula | ¬ occursIn (free_ y) F} :=
  by
  apply Set.LeftInvOn.injOn
  apply OpenFormulaLeftInvOn


lemma CloseFormulaInjOn
  (y : String)
  (k : ℕ) :
  Set.InjOn (closeFormulaAux (free_ y) k) {F : Formula | Formula.lc_at k F} :=
  by
  apply Set.LeftInvOn.injOn
  apply CloseFormulaLeftInvOn


example
  (F G : Formula)
  (k : ℕ)
  (y : String)
  (h1 : ¬ occursIn (free_ y) F)
  (h2 : ¬ occursIn (free_ y) G)
  (h3 : openFormulaAux k (free_ y) F = openFormulaAux k (free_ y) G) :
  F = G :=
  by
  apply OpenFormulaInjOn
  · simp only [Set.mem_setOf_eq]
    exact h1
  · simp only [Set.mem_setOf_eq]
    exact h2
  · exact h3


--------------------------------------------------


lemma OpenVarFreeStringSet
  (v : Var)
  (k : ℕ)
  (y : String) :
  (openVar k (free_ y) v).freeStringSet ⊆ v.freeStringSet ∪ {y} :=
  by
  cases v
  case free_ x =>
    simp only [openVar]
    simp only [Var.freeStringSet]
    simp only [Finset.singleton_union, Finset.singleton_subset_iff, Finset.mem_insert, Finset.mem_singleton]
    left
    exact True.intro
  case bound_ i =>
    simp only [openVar]
    split
    case isTrue c1 =>
      simp only [Var.freeStringSet]
      simp only [Finset.empty_union, subset_refl]
    case isFalse c1 =>
      simp only [Var.freeStringSet]
      simp only [Finset.empty_union, Finset.subset_singleton_iff, Finset.empty_ne_singleton]
      left
      exact True.intro


lemma CloseVarFreeStringSet
  (v : Var)
  (y : String)
  (k : ℕ) :
  (closeVar (free_ y) k v).freeStringSet ⊆ v.freeStringSet \ {y} :=
  by
  cases v
  case free_ x =>
    simp only [closeVar]
    split
    case isTrue c1 =>
      simp only [Var.freeStringSet]
      simp only [Finset.empty_subset]
    case isFalse c1 =>
      simp only [free_.injEq] at c1
      simp only [Var.freeStringSet]
      simp only [Finset.singleton_subset_iff, Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · exact True.intro
      · intro contra
        apply c1
        rewrite [contra]
        apply Eq.refl
  case bound_ i =>
    simp only [closeVar]
    simp only [Var.freeStringSet]
    simp only [Finset.empty_sdiff, subset_refl]


--------------------------------------------------


lemma OpenVarFreeVarSet
  (v : Var)
  (k : ℕ)
  (y : String) :
  (openVar k (free_ y) v).freeVarSet ⊆ v.freeVarSet ∪ {free_ y} :=
  by
  cases v
  case free_ x =>
    simp only [openVar]
    simp only [Var.freeVarSet]
    simp only [Finset.singleton_union, Finset.singleton_subset_iff, Finset.mem_insert, Finset.mem_singleton]
    left
    exact True.intro
  case bound_ i =>
    simp only [openVar]
    split
    case isTrue c1 =>
      simp only [Var.freeVarSet]
      simp only [Finset.empty_union, subset_refl]
    case _ c1 =>
      simp only [Var.freeVarSet]
      simp only [Finset.empty_union, Finset.subset_singleton_iff, Finset.empty_ne_singleton]
      left
      exact True.intro


lemma CloseVarFreeVarSet
  (v : Var)
  (y : String)
  (k : ℕ) :
  (closeVar (free_ y) k v).freeVarSet ⊆ v.freeVarSet \ {free_ y} :=
  by
  cases v
  case free_ x =>
    simp only [closeVar]
    split
    case isTrue c1 =>
      simp only [Var.freeVarSet]
      simp only [Finset.empty_subset]
    case isFalse c1 =>
      simp only [Var.freeVarSet]
      simp only [Finset.singleton_subset_iff, Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · exact True.intro
      · intro contra
        apply c1
        rewrite [contra]
        apply Eq.refl
  case bound_ i =>
    simp only [closeVar]
    simp only [Var.freeVarSet]
    simp only [Finset.empty_sdiff, subset_refl]


lemma OpenFormulaFreeVarSet
  (F : Formula)
  (k : ℕ)
  (y : String) :
  (openFormulaAux k (free_ y) F).freeVarSet ⊆ F.freeVarSet ∪ {free_ y} :=
  by
  induction F generalizing k
  case pred_ X vs =>
    simp only [openFormulaAux]
    simp only [Formula.freeVarSet]
    simp only [Finset.biUnion_subset_iff_forall_subset, List.mem_toFinset, List.mem_map]
    intro v a1
    obtain ⟨u, ⟨a1_left, a1_right⟩⟩ := a1
    rewrite [← a1_right]
    trans (Var.freeVarSet u ∪ {free_ y})
    · apply OpenVarFreeVarSet
    · apply Finset.union_subset_union_left
      apply Finset.subset_biUnion_of_mem
      simp only [List.mem_toFinset]
      exact a1_left
  case not_ phi phi_ih =>
    simp only [openFormulaAux]
    simp only [Formula.freeVarSet]
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    specialize phi_ih k
    specialize psi_ih k
    simp only [openFormulaAux]
    simp only [Formula.freeVarSet]
    simp only [Finset.union_subset_iff]
    constructor
    · trans (phi.freeVarSet ∪ {free_ y})
      · exact phi_ih
      · apply Finset.union_subset_union
        · exact Finset.subset_union_left
        · apply Set.Subset.refl
    · trans (psi.freeVarSet ∪ {free_ y})
      · exact psi_ih
      · apply Finset.union_subset_union
        · exact Finset.subset_union_right
        · apply Set.Subset.refl
  case forall_ phi phi_ih =>
    simp only [openFormulaAux]
    simp only [Formula.freeVarSet]
    apply phi_ih


lemma CloseFormulaFreeVarSet
  (F : Formula)
  (y : String)
  (k : ℕ) :
  (closeFormulaAux (free_ y) k F).freeVarSet ⊆ F.freeVarSet \ {free_ y} :=
  by
  induction F generalizing k
  case pred_ X vs =>
    simp only [closeFormulaAux]
    simp only [Formula.freeVarSet]
    simp only [Finset.biUnion_subset_iff_forall_subset, List.mem_toFinset, List.mem_map]
    intro v a1
    obtain ⟨u, ⟨a1_left, a1_right⟩⟩ := a1
    rewrite [← a1_right]
    trans (u.freeVarSet \ {free_ y})
    · apply CloseVarFreeVarSet
    · apply Finset.sdiff_subset_sdiff
      · apply Finset.subset_biUnion_of_mem
        simp only [List.mem_toFinset]
        exact a1_left
      · apply Set.Subset.refl
  case not_ phi phi_ih =>
    simp only [closeFormulaAux]
    simp only [Formula.freeVarSet]
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    specialize phi_ih k
    specialize psi_ih k
    simp only [closeFormulaAux]
    simp only [Formula.freeVarSet]
    simp only [Finset.union_subset_iff]
    constructor
    · trans (phi.freeVarSet \ {free_ y})
      · exact phi_ih
      · apply Finset.sdiff_subset_sdiff
        · exact Finset.subset_union_left
        · apply Set.Subset.refl
    · trans (psi.freeVarSet \ {free_ y})
      · exact psi_ih
      · apply Finset.sdiff_subset_sdiff
        · exact Finset.subset_union_right
        · apply Set.Subset.refl
  case forall_ phi phi_ih =>
    simp only [closeFormulaAux]
    simp only [Formula.freeVarSet]
    apply phi_ih


--------------------------------------------------


lemma shift_openVar
  (D : Type)
  (V : VarAssignment D)
  (k : ℕ)
  (y : String)
  (d : D) :
  shift D (V ∘ openVar k (free_ y)) d =
    shift D V d ∘ openVar (k + 1) (free_ y) :=
  by
  funext v
  simp only [Function.comp_apply]
  cases v
  case free_ x =>
    simp only [openVar]
    simp only [shift]
    simp only [Function.comp_apply]
    simp only [openVar]
  case bound_ i =>
    cases i
    case zero =>
      simp only [openVar]
      split
      case isTrue c1 =>
        simp only [Nat.right_eq_add, Nat.add_eq_zero_iff] at c1
        obtain ⟨c1_left, c1_right⟩ := c1
        simp only [one_ne_zero] at c1_right
      case isFalse c1 =>
        simp only [shift]
    case succ i =>
      simp only [openVar]
      split
      case isTrue c1 =>
        simp only [Nat.add_right_cancel_iff] at c1

        simp only [shift]
        simp only [Function.comp_apply]
        simp only [openVar]
        split
        case isTrue c2 =>
          apply Eq.refl
        case isFalse c2 =>
          contradiction
      case isFalse c1 =>
        simp only [Nat.add_right_cancel_iff] at c1

        simp only [shift]
        simp only [Function.comp_apply]
        simp only [openVar]
        split
        case isTrue c2 =>
          contradiction
        case isFalse c2 =>
          apply Eq.refl


lemma Holds_openFormulaAux
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (F : Formula)
  (k : Nat)
  (y : String) :
  Holds D I (V ∘ openVar k (free_ y)) F ↔
    Holds D I V (openFormulaAux k (free_ y) F) :=
  by
  induction F generalizing V k
  case pred_ X vs =>
    simp only [openFormulaAux]
    simp only [Holds]
    simp only [List.map_map]
  case not_ phi phi_ih =>
    simp only [openFormulaAux]
    simp only [Holds]
    congr! 1
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [openFormulaAux]
    simp only [Holds]
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ phi phi_ih =>
    simp only [openFormulaAux]
    simp only [Holds]
    apply forall_congr'
    intro d
    rewrite [<- phi_ih]
    congr! 1
    apply shift_openVar


--------------------------------------------------


lemma shift_openVarList
  (D : Type)
  (V : VarAssignment D)
  (k : ℕ)
  (zs : List String)
  (d : D) :
  shift D (V ∘ openVarList k (zs.map Var.free_)) d = shift D V d ∘ openVarList (k + 1) (zs.map Var.free_) :=
  by
  funext v
  simp only [Function.comp_apply]
  cases v
  case free_ a =>
    simp only [openVarList]
    simp only [shift]
    simp only [Function.comp_apply]
    simp only [openVarList]
  case bound_ n =>
    simp only [openVarList]
    split
    case isTrue c1 =>
      cases n
      case zero =>
        simp only [shift]
      case succ n =>
        simp only [shift]
        simp only [Function.comp_apply]
        simp only [openVarList]
        split
        case isTrue c2 =>
          apply Eq.refl
        case isFalse c2 =>
          simp only [Order.lt_add_one_iff, Order.add_one_le_iff] at c1
          contradiction
    case isFalse c1 =>
      cases n
      case zero =>
        exfalso
        apply c1
        apply Nat.zero_lt_succ
      case succ n =>
        simp only [Order.lt_add_one_iff, Order.add_one_le_iff] at c1

        have s1 : n + 1 - (k + 1) = n - k :=
        by
          apply Nat.add_sub_add_right
        rewrite [s1]

        split
        case isTrue c2 =>
          simp only [List.getElem_map]
          simp only [shift]
          simp only [Function.comp_apply]
          simp only [openVarList]
          split
          case isTrue c3 =>
            contradiction
          case isFalse c3 =>
            simp only [List.getElem_map]
        case isFalse c2 =>
          have s2 : (n + 1) - zs.length = (n - zs.length) + 1 :=
          by
            apply Nat.succ_sub
            trans (n - k)
            · simp only [List.length_map, not_lt] at c2
              exact c2
            · apply Nat.sub_le

          simp only [List.length_map]
          rewrite [s2]
          simp only [shift]
          simp only [Function.comp_apply]
          simp only [openVarList]
          split
          case isTrue c3 =>
            contradiction
          case isFalse c3 =>
            simp only [List.length_map]


lemma Holds_openFormulaListAux
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (zs : List String)
  (k : Nat)
  (F : Formula) :
  Holds D I (V ∘ openVarList k (zs.map Var.free_)) F ↔
    Holds D I V (openFormulaListAux k (zs.map Var.free_) F) :=
  by
  induction F generalizing V k
  case pred_ X vs =>
    simp only [openFormulaListAux]
    simp only [Holds]
    simp only [List.map_map]
  case not_ phi phi_ih =>
    simp only [openFormulaListAux]
    simp only [Holds]
    congr! 1
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [openFormulaListAux]
    simp only [Holds]
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ phi phi_ih =>
    simp only [openFormulaListAux]
    simp only [Holds]
    apply forall_congr'
    intro d
    rewrite [← phi_ih]
    congr! 1
    apply shift_openVarList


--------------------------------------------------


lemma Formula.lc_at_instantiate_id
  (F : Formula)
  (k : ℕ)
  (zs : List String)
  (h1 : F.lc_at k) :
  Formula.instantiate k (zs.map Var.free_) F = F :=
  by
  induction F generalizing k
  case pred_ X vs =>
    simp only [Formula.lc_at] at h1

    simp only [Formula.instantiate]
    congr
    apply List.fun_is_id_on_mem_imp_map_eq_self
    intro v a1
    specialize h1 v a1
    cases v
    case free_ x =>
      simp only [Var.instantiate]
    case bound_ i =>
      cases i
      case zero =>
        simp only [Var.lc_at] at h1
        simp only [Var.instantiate]
        split
        case isTrue c1 =>
          apply Eq.refl
        case isFalse c1 =>
          contradiction
      case succ i =>
        simp only [Var.lc_at] at h1
        simp only [Var.instantiate]
        split
        case isTrue c1 =>
          apply Eq.refl
        case isFalse c1 =>
          contradiction
  case not_ phi phi_ih =>
    simp only [Formula.lc_at] at h1

    simp only [Formula.instantiate]
    congr!
    apply phi_ih
    exact h1
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.lc_at] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    simp only [Formula.instantiate]
    congr
    · apply phi_ih
      exact h1_left
    · apply psi_ih
      exact h1_right
  case forall_ x phi phi_ih =>
    simp only [Formula.lc_at] at h1

    simp only [Formula.instantiate]
    congr
    apply phi_ih
    exact h1


lemma lc_at_instantiate
  (F : Formula)
  (k : ℕ)
  (zs : List String) :
  Formula.lc_at k (instantiate k (zs.map Var.free_) F) ↔ Formula.lc_at (k + zs.length) F :=
  by
  induction F generalizing k zs
  case pred_ X vs =>
    simp only [Formula.instantiate]
    simp only [Formula.lc_at]
    constructor
    · intro a1 v a2
      specialize a1 (Var.instantiate k (List.map free_ zs) v)
      simp only [List.mem_map, forall_exists_index, and_imp] at a1
      specialize a1 v a2
      simp only [forall_const] at a1

      cases v
      case free_ x =>
        simp only [Var.lc_at]
      case bound_ i =>
        simp only [Var.lc_at]
        simp only [Var.instantiate] at a1
        split at a1
        case isTrue c1 =>
          apply Nat.lt_add_right
          exact c1
        case isFalse c1 =>
          split at a1
          case isTrue c2 =>
            simp only [List.length_map] at c2
            apply lt_add_of_tsub_lt_left
            exact c2
          case isFalse c2 =>
            simp only [Var.lc_at] at a1
            simp only [List.length_map, add_lt_iff_neg_right, not_lt_zero] at a1
    · intro a1 v a2
      cases v
      case free_ x =>
        simp only [Var.lc_at]
      case bound_ i =>
        simp only [Var.lc_at]
        simp only [List.mem_map] at a2
        obtain ⟨v, ⟨a2_left, a2_right⟩⟩ := a2

        specialize a1 v a2_left

        cases v
        case free_ x =>
          simp only [Var.instantiate] at a2_right
          contradiction
        case bound_ j =>
          simp only [Var.instantiate] at a2_right
          split at a2_right
          case isTrue c1 =>
            simp only [bound_.injEq] at a2_right
            rewrite [← a2_right]
            exact c1
          case isFalse c1 =>
            simp only [List.length_map, List.getElem_map] at a2_right
            split at a2_right
            case isTrue c2 =>
              contradiction
            case isFalse c2 =>
              exfalso
              apply c2
              apply Nat.sub_lt_left_of_lt_add
              · simp only [not_lt] at c1
                exact c1
              · simp only [Var.lc_at] at a1
                exact a1
  case not_ phi phi_ih =>
    simp only [Formula.instantiate]
    simp only [Formula.lc_at]
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.instantiate]
    simp only [Formula.lc_at]
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ _ phi phi_ih =>
    simp only [Formula.instantiate]
    simp only [Formula.lc_at]
    rewrite [phi_ih]
    congr! 1
    apply Nat.add_right_comm


lemma Var.instantiate_append
  (k : ℕ)
  (zs zs' : List Var)
  (v : Var)
  (h1 : ∀ (z' : Var), z' ∈ zs' → z'.isFree) :
  Var.instantiate k zs (Var.instantiate (k + List.length zs) zs' v) = Var.instantiate k (zs ++ zs') v :=
  by
  rcases v with _ | i; · rfl
  conv => rhs; simp only [Var.instantiate]
  split_ifs
  case pos c1 =>
    have s1 : i < k + zs.length := by exact Nat.lt_add_right zs.length c1
    have s2 : ¬ k ≤ i := by exact Nat.not_le_of_lt c1

    simp only [instantiate]
    split_ifs
    simp
    intro a1
    contradiction
  case neg c1 c2 =>
    simp at c2
    simp
    simp only [instantiate]
    split_ifs
    case pos c3 =>
      simp
      split_ifs
      case pos c4 =>
        have s1 : ¬ i - k < zs.length := by omega
        contradiction
      case neg c4 =>
        have s1 : i - k < zs.length := by omega
        contradiction
    case pos c3 c4 =>
      have s1 : ¬ zs.length + zs'.length ≤ i - k := by omega
      contradiction
    case neg c3 c4 =>
      simp
      split_ifs
      case pos c5 =>
        have s1 : ¬ zs.length + zs'.length ≤ i - k := by omega
        contradiction
      case pos c5 c6 =>
        have s1 : ¬ zs.length + zs'.length ≤ i - k := by omega
        contradiction
      case neg c5 c6 =>
        simp
        omega
  case pos c1 c2 =>
    simp only [instantiate]
    split_ifs
    case pos c3 =>
      simp
      split_ifs
      case pos c4 =>
        apply List.getElem_append_left'
      case neg c4 =>
        have s1 : i - k < zs.length := by omega
        contradiction
    case pos c3 c4 =>
      specialize h1 zs'[i - (k + zs.length)]
      simp at h1
      simp only [IsFreeIffExistsString zs'[i - (k + zs.length)]] at h1
      obtain ⟨x, a1⟩ := h1
      rw [a1]
      simp
      rw [← a1]
      obtain s1 := List.getElem_append c2
      rw [s1]
      have s2 : ¬ i - k < zs.length := by omega
      split_ifs
      congr 1
      omega
    case neg c3 c4 =>
      have s1 : ¬ i - k < (zs ++ zs').length :=
      by
        simp
        omega
      contradiction


lemma Formula.instantiate_append
  (k : ℕ)
  (zs zs' : List Var)
  (F : Formula)
  (h1 : ∀ (z' : Var), z' ∈ zs' → z'.isFree) :
  Formula.instantiate k zs (Formula.instantiate (k + List.length zs) zs' F) = Formula.instantiate k (zs ++ zs') F :=
  by
  induction F generalizing k
  case pred_ X vs =>
    simp only [Formula.instantiate]
    simp
    intro v _
    apply Var.instantiate_append
    exact h1
  case not_ phi phi_ih =>
    simp only [Formula.instantiate]
    congr! 1
    exact phi_ih k
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.instantiate]
    congr! 1
    · exact phi_ih k
    · exact psi_ih k
  case forall_ x phi phi_ih =>
    simp only [Formula.instantiate]
    congr! 1
    simp only [← phi_ih]
    congr! 2
    linarith


lemma lc_at_imp_lc_instantiate
  (F : Formula)
  (zs : List String)
  (h1 : lc_at zs.length F) :
  lc (instantiate 0 (zs.map Var.free_) F) :=
  by
  induction F generalizing zs
  case pred_ X vs =>
    simp only [Formula.lc_at] at h1

    simp only [Formula.instantiate]
    apply Formula.lc.pred_
    intro v a1
    cases v
    case _ x =>
      simp only [isFree]
    case _ i =>
      simp at a1
      apply Exists.elim a1
      intro z a2
      cases a2
      case _ a2_left a2_right =>
        specialize h1 z a2_left

        cases z
        case _ x =>
          simp only [Var.instantiate] at a2_right
          simp at a2_right
        case _ j =>
          simp only [Var.lc_at] at h1

          simp only [Var.instantiate] at a2_right
          simp at a2_right
          split at a2_right
          case _ c1 =>
            contradiction
          case _ c1 =>
            contradiction
  case not_ phi phi_ih =>
    simp only [Formula.lc_at] at h1

    apply Formula.lc.not_
    exact phi_ih zs h1
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.lc_at] at h1
    cases h1
    case _ h1_left h1_right =>
      apply Formula.lc.imp_
      · exact phi_ih zs h1_left
      · exact psi_ih zs h1_right
  case forall_ x phi phi_ih =>
    simp only [Formula.lc_at] at h1

    specialize phi_ih (default :: zs)
    simp at phi_ih
    specialize phi_ih h1

    simp only [Formula.instantiate]
    apply Formula.lc.forall_ x (Formula.instantiate (0 + 1) (List.map free_ zs) phi) default
    simp

    obtain s1 := Formula.instantiate_append 0 [Var.free_ default] (zs.map Var.free_) phi
    simp at s1
    simp only [isFree] at s1
    simp at s1

    simp only [s1]
    exact phi_ih


lemma lc_at_imp_lc
  (F : Formula)
  (h1 : lc_at 0 F) :
  lc F :=
  by
  induction F
  case pred_ X vs =>
    simp only [Formula.lc_at] at h1

    apply Formula.lc.pred_
    intro v a1
    specialize h1 v a1
    cases v
    case _ x =>
      simp only [Var.isFree]
    case _ i =>
      simp only [Var.lc_at] at h1
      simp at h1
  case not_ phi phi_ih =>
    simp only [Formula.lc_at] at h1

    apply Formula.lc.not_
    exact phi_ih h1
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.lc_at] at h1

    cases h1
    case _ h1_left h1_right =>
      apply Formula.lc.imp_
      · exact phi_ih h1_left
      · exact psi_ih h1_right
  case forall_ x phi _ =>
    simp only [Formula.lc_at] at h1
    simp at h1

    apply Formula.lc.forall_ x phi default
    apply lc_at_imp_lc_instantiate phi [default]
    simp
    exact h1


lemma lc_imp_lc_at
  (F : Formula)
  (h1 : lc F) :
  lc_at 0 F :=
  by
  induction h1
  case pred_ X vs ih =>
    simp only [Formula.lc_at]
    intro v a1
    specialize ih v a1
    cases v
    case _ x =>
      simp only [Var.lc_at]
    case _ i =>
      simp only [isFree] at ih
  case not_ phi ih_1 ih_2 =>
    simp only [Formula.lc_at]
    exact ih_2
  case imp_ phi psi phi_ih_1 psi_ih_1 phi_ih_2 psi_ih_2 =>
    simp only [Formula.lc_at]
    constructor
    · exact phi_ih_2
    · exact psi_ih_2
  case forall_ x phi z ih_1 ih_2 =>
    simp only [Formula.lc_at]
    simp

    obtain s1 := lc_at_instantiate phi 0 [z]
    simp at s1
    simp only [← s1]
    exact ih_2


lemma lc_at_iff_lc
  (F : Formula) :
  lc_at 0 F ↔ lc F :=
  by
  constructor
  · intro a1
    exact lc_at_imp_lc F a1
  · intro a1
    exact lc_imp_lc_at F a1

--------------------------------------------------

lemma free_var_list_to_string_list
  (vs : List Var)
  (h1 : ∀ (v : Var), v ∈ vs → Var.lc_at 0 v) :
  ∃ xs, vs = List.map free_ xs :=
  by
  induction vs
  case nil =>
    apply Exists.intro []
    simp
  case cons hd tl ih =>
    simp at h1
    cases h1
    case intro h1_left h1_right =>
      specialize ih h1_right
      apply Exists.elim ih
      intro xs a1
      cases hd
      case free_ x =>
        apply Exists.intro (x :: xs)
        simp
        exact a1
      case bound_ i =>
        simp only [Var.lc_at] at h1_left
        simp at h1_left


theorem shift_instantiate
  (D : Type)
  (V : VarAssignment D)
  (zs : List String)
  (k : ℕ)
  (d : D) :
  shift D (V ∘ Var.instantiate k (List.map free_ zs)) d =
    shift D V d ∘ Var.instantiate (k + 1) (List.map free_ zs) :=
  by
  funext v
  simp
  cases v
  case _ x =>
    simp only [Var.instantiate]
    simp only [shift]
    simp
    rfl
  case _ i =>
    cases i
    case zero =>
      simp only [shift]
      simp only [Var.instantiate]
      simp
    case succ i =>
        simp only [shift]
        simp only [Var.instantiate]
        simp
        split_ifs
        case _ c1 =>
          have s1 : i + 1 < k + 1
          linarith
          simp only [if_pos s1]
          simp only [Var.instantiate]
          simp only [c1]
          simp
        case _ c1 c2 =>
          have s1 : ¬ i + 1 < k + 1
          linarith
          simp only [if_neg s1]
          simp only [Var.instantiate]
          simp only [c1]
          simp
          simp only [c2]
          simp
        case _ c1 c2 =>
          simp
          simp only [Var.instantiate]
          simp only [c1]
          simp
          simp only [c2]
          simp


lemma Holds_instantiate
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (zs : List String)
  (k : Nat)
  (F : Formula) :
  Holds D I (V ∘ Var.instantiate k (zs.map Var.free_)) F ↔
    Holds D I V (Formula.instantiate k (zs.map Var.free_) F) :=
  by
  induction F generalizing V k
  case pred_ X vs =>
    simp only [Holds]
    congr! 1
    simp only [Formula.instantiate]
    simp only [Holds]
    simp only [List.map_map]
  case not_ phi phi_ih =>
    simp only [Holds]
    congr! 1
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Holds]
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ _ phi phi_ih =>
    simp only [Holds]
    apply forall_congr'
    intro d
    simp only [← phi_ih]
    congr!
    apply shift_instantiate


theorem shift_list_instantiate
  (D : Type)
  (V : VarAssignment D)
  (xs : List String) :
  V ∘ Var.instantiate 0 (List.map free_ xs) =
    shift_list D V (List.map (V ∘ free_) xs) :=
  by
  induction xs
  case nil =>
    funext v
    simp
    simp only [shift_list]
    cases v
    case _ x =>
      simp only [Var.instantiate]
    case _ i =>
      simp only [Var.instantiate]
      split
      case _ c1 =>
        rfl
      case _ c1 =>
        simp
  case _ hd tl ih =>
    funext v
    simp
    simp only [shift_list]
    cases v
    case _ x =>
      simp only [shift]
      simp only [← ih]
      simp only [Var.instantiate]
      simp
      rfl
    case _ i =>
      cases i
      case zero =>
        simp only [shift]
        simp only [Var.instantiate]
        simp
      case succ i =>
        simp only [shift]
        simp only [← ih]
        simp
        simp only [Var.instantiate]
        simp

--------------------------------------------------

lemma shift_extract1
  (D : Type)
  (V : VarAssignment D)
  (k : ℕ)
  (z : String)
  (d : D) :
  shift D V d ∘ Var.abstract1 (free_ z) (k + 1) = shift D (V ∘ Var.abstract1 (free_ z) k) d :=
  by
  funext v
  simp
  cases v
  case _ x =>
    conv =>
      rhs
      simp only [shift]
      simp
    simp only [Var.abstract1]
    simp
    split_ifs
    case _ c1 =>
      simp only [shift]
    case _ c1 =>
      simp only [shift]
  case _ i =>
    cases i
    case zero =>
      conv =>
        rhs
        simp only [shift]
      simp only [Var.abstract1]
      simp
      simp only [shift]
    case succ i =>
      conv =>
        rhs
        simp only [shift]
        simp
        simp only [Var.abstract1]
      simp only [Var.abstract1]
      split
      case _ c1 =>
        have s1 : i < k
        linarith
        simp only [if_pos s1]
        simp only [shift]
      case _ c1 =>
        simp at c1
        have s1 : ¬ i < k
        linarith
        simp only [if_neg s1]
        simp only [shift]


lemma Holds_abstract_instantiate
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (z : String)
  (F : Formula)
  (k : ℕ)
  (h1 : ¬ occursIn (free_ z) F)
  (h2 : F.lc_at k) :
  Holds D I V F ↔ Holds D I (V ∘ Var.abstract1 (free_ z) k) (Formula.instantiate k [free_ z] F) :=
  by
  induction F generalizing V k
  case pred_ X vs =>
    simp only [occursIn] at h1
    simp only [Formula.lc_at] at h2

    simp only [Formula.instantiate]
    simp only [Holds]
    congr! 1
    simp
    intro v a1
    specialize h2 v a1
    cases v
    case _ x =>
      simp only [Var.instantiate]
      simp only [Var.abstract1]

      have s1 : ¬ free_ z = free_ x
      intro contra
      apply h1
      simp only [contra]
      exact a1

      simp only [if_neg s1]
    case _ i =>
      simp only [Var.lc_at] at h2

      simp only [Var.instantiate]
      simp
      split_ifs
      simp only [Var.abstract1]
      simp only [if_pos h2]
  case not_ phi phi_ih =>
    simp only [occursIn] at h1
    simp only [Formula.lc_at] at h2

    simp only [Holds]
    congr! 1
    apply phi_ih V k h1 h2
  case imp_ phi psi phi_ih psi_ih =>
    simp only [occursIn] at h1
    push_neg at h1
    simp only [Formula.lc_at] at h2

    cases h1
    case _ h1_left h1_right =>
      cases h2
      case _ h2_left h2_right =>
        simp only [Holds]
        congr! 1
        · apply phi_ih V k h1_left h2_left
        · apply psi_ih V k h1_right h2_right
  case forall_ x phi phi_ih =>
    simp only [occursIn] at h1
    simp only [Formula.lc_at] at h2

    simp only [Formula.instantiate]
    simp only [Holds]
    apply forall_congr'
    intro d
    specialize phi_ih (shift D V d) (k + 1) h1 h2
    simp only [phi_ih]
    congr! 1
    apply shift_extract1

--------------------------------------------------

example
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (τ : String → ℕ → Formula)
  (F : Formula)
  (h1 : F.lc) :
  Holds D I V (F.predSub τ) ↔
    Holds D (Interpretation.usingPred D I fun (X : String) (ds : List D) => Holds D I (shift_list D V ds) (τ X ds.length)) V F :=
  by
  induction h1 generalizing V
  case pred_ X vs ih =>
    simp only [predSub]
    simp only [Interpretation.usingPred]
    simp only [Holds]
    simp

    have s1 : ∀ (v : Var), v ∈ vs → Var.lc_at 0 v
    intro v a1
    specialize ih v a1
    cases v
    case _ x =>
      simp only [Var.lc_at]
    case _ i =>
      simp only [Var.isFree] at ih

    obtain s2 := free_var_list_to_string_list vs s1
    apply Exists.elim s2
    intro zs a1

    obtain s3 := Holds_instantiate D I V zs 0 (τ X (List.length vs))
    simp only [← a1] at s3
    simp only [← s3]
    clear s2

    congr! 1
    simp only [a1]
    simp
    obtain s4 := shift_list_instantiate D V zs
    simp only [s4]
  case not_ phi ih_1 ih_2 =>
    simp only [Holds]
    congr! 1
    apply ih_2
  case imp_ phi psi phi_ih_1 psi_ih_1 phi_ih_2 psi_ih_2 =>
    simp only [Holds]
    congr! 1
    · apply phi_ih_2
    · apply psi_ih_2
  case forall_ x phi z ih_1 ih_2 =>
    simp only [Holds]
    apply forall_congr'
    intro d

    simp only [← lc_at_iff_lc] at ih_1
    obtain s1 := lc_at_instantiate phi 0 [z]
    simp at s1
    simp only [s1] at ih_1
    clear s1

    specialize ih_2 (shift D V d)

    obtain s2 := Holds_abstract_instantiate


    sorry


example
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (τ : String → ℕ → Formula)
  (zs : List String)
  (F : Formula)
  (h1 : F.lc_at 0) :
  Holds D I V (F.predSub τ) ↔
    Holds D (Interpretation.usingPred D I fun (X : String) (ds : List D) => Holds D I (shift_list D V ds) (τ X ds.length)) V F :=
  by
  induction F generalizing V
  case pred_ X vs =>
    simp only [predSub]
    simp only [Interpretation.usingPred]
    simp only [Holds]
    simp

    have s1 : ∀ (v : Var), v ∈ vs → Var.lc_at 0 v
    intro v a1
    specialize h1 v a1
    cases v
    case _ x =>
      simp only [Var.lc_at]
    case _ i =>
      simp only [Var.lc_at] at h1
      simp at h1

    obtain s2 := free_var_list_to_string_list vs s1
    apply Exists.elim s2
    intro zs a1

    obtain s3 := Holds_instantiate D I V zs 0 (τ X (List.length vs))
    simp only [← a1] at s3
    simp only [← s3]
    clear s2

    congr! 1
    simp only [a1]
    simp
    obtain s4 := shift_list_instantiate D V zs
    simp only [s4]
  case forall_ x phi phi_ih =>
    simp only [Formula.lc_at] at h1

    simp only [Holds]
    apply forall_congr'
    intro d

    obtain s1 := Holds_abstract_instantiate
    sorry
  all_goals
    sorry


example
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (x : String)
  (F : Formula)
  (z : String)
  (h1 : (free_ z) ∉ F.freeVarSet) :
  Holds D I V (forall_ x F) ↔ ∀ (d : D), Holds D I (Function.updateITE V (free_ z) d) (instantiate 0 [free_ z] F) :=
  by
  simp only [Holds]
  apply forall_congr'
  intro d


  induction F generalizing V
  case pred_ X vs =>
    simp only [Formula.freeVarSet] at h1
    simp at h1
    simp only [Formula.instantiate]
    simp only [Holds]
    simp
    congr! 1
    simp only [List.map_eq_map_iff]
    intro v a1
    simp

    cases v
    case _ b =>
      simp only [Var.instantiate]
      simp only [shift]
      specialize h1 (free_ b) a1
      simp only [Var.freeVarSet] at h1
      simp at h1
      simp only [Function.updateITE]
      split
      case isTrue c1 =>
        simp only [free_.injEq] at c1
        rewrite [c1] at h1
        contradiction
      case isFalse c1 =>
        rfl
    case _ i =>
      cases i
      case zero =>
        simp only [Var.instantiate]
        simp only [shift]
        simp
        simp only [Function.updateITE]
        simp
      case succ i =>
        simp only [Var.instantiate]
        simp only [shift]
        simp
        simp only [Function.updateITE]
        simp
  case forall_ x' phi phi_ih =>
    simp only [Formula.freeVarSet] at h1
    simp only [Formula.instantiate]
    simp only [Holds]
    apply forall_congr'
    intro d'
    specialize phi_ih V h1
    simp
    sorry
  all_goals
    sorry


end LN


--#lint
