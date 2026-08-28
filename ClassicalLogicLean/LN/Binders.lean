import ClassicalLogicLean.LN.Formula


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


namespace LN

open Var Formula


/--
  Var.isFree v := True if and only if v is a free variable.
-/
def Var.isFree : Var → Prop
  | free_ _ => True
  | bound_ _ => False

instance (v : Var) : Decidable v.isFree :=
  by
  cases v
  case free_ x =>
    simp only [Var.isFree]
    exact instDecidableTrue
  case bound_ i =>
    simp only [Var.isFree]
    exact instDecidableFalse


/--
  Var.isBound v := True if and only if v is a bound variable.
-/
def Var.isBound : Var → Prop
  | free_ _ => False
  | bound_ _ => True

instance (v : Var) : Decidable v.isBound :=
  by
  cases v
  case free_ x =>
    simp only [Var.isBound]
    exact instDecidableFalse
  case bound_ i =>
    simp only [Var.isBound]
    exact instDecidableTrue


--------------------------------------------------


/--
  Formula.varSet F := The set of all of the variables that have an occurrence in the formula F.
-/
def Formula.varSet : Formula → Finset Var
  | pred_ _ vs => vs.toFinset
  | not_ phi => phi.varSet
  | imp_ phi psi => phi.varSet ∪ psi.varSet
  | forall_ _ phi => phi.varSet


/--
  occursIn v F := True if and only if there is an occurrence of the variable v in the formula F.
-/
def occursIn (v : Var) : Formula → Prop
  | pred_ _ vs => v ∈ vs
  | not_ phi => occursIn v phi
  | imp_ phi psi => occursIn v phi ∨ occursIn v psi
  | forall_ _ phi => occursIn v phi


instance (v : Var) (F : Formula) : Decidable (occursIn v F) :=
  by
  induction F
  all_goals
    simp only [occursIn]
    infer_instance


--------------------------------------------------


/--
  Helper function for occursFreeIn.
-/
def lift : Var → Var
  | free_ x => free_ x
  | bound_ i => bound_ (i + 1)


/--
  occursFreeIn v F :=
  If v = free_ x then true if and only if there is an occurrence of free_ x in the formula F.
  If v = bound_ i then true if and only if there is an occurrence of a variable of the form bound_ _ that is out of scope by i + 1.
-/
def occursFreeIn (v : Var) : Formula → Prop
  | pred_ _ vs => v ∈ vs
  | not_ phi => occursFreeIn v phi
  | imp_ phi psi => occursFreeIn v phi ∨ occursFreeIn v psi
  | forall_ _ phi => occursFreeIn (lift v) phi


--------------------------------------------------


/--
  Helper function for Formula.freeVarSet
-/
def Var.freeVarSet : Var → Finset Var
  | free_ x => {free_ x}
  | bound_ _ => ∅


/--
  Formula.freeVarSet F := The set of all of the free variables that have an occurrence in the formula F.
-/
def Formula.freeVarSet : Formula → Finset Var
  | pred_ _ vs => vs.toFinset.biUnion Var.freeVarSet
  | not_ phi => phi.freeVarSet
  | imp_ phi psi => phi.freeVarSet ∪ psi.freeVarSet
  | forall_ _ phi => phi.freeVarSet


--------------------------------------------------


/--
  Helper function for Formula.boundVarSet
-/
def Var.boundVarSet : Var → Finset Var
  | free_ _ => ∅
  | bound_ i => {bound_ i}


/--
  Formula.boundVarSet F := The set of all of the bound variables that have an occurrence in the formula F.
-/
def Formula.boundVarSet : Formula → Finset Var
  | pred_ _ vs => vs.toFinset.biUnion Var.boundVarSet
  | not_ phi => phi.boundVarSet
  | imp_ phi psi => phi.boundVarSet ∪ psi.boundVarSet
  | forall_ _ phi => phi.boundVarSet


--------------------------------------------------


/--
  Formula.freeVarSet' F := The set of all of the free variables that have an occurrence in the formula F.
-/
def Formula.freeVarSet' (F : Formula) : Finset Var :=
  F.varSet.filter Var.isFree

/--
  Formula.boundVarSet' F := The set of all of the bound variables that have an occurrence in the formula F.
-/
def Formula.boundVarSet' (F : Formula) : Finset Var :=
  F.varSet.filter Var.isBound


--------------------------------------------------


/--
  Helper function for Formula.freeStringSet
-/
def Var.freeStringSet : Var → Finset String
  | free_ x => {x}
  | bound_ _ => ∅

/--
  Formula.freeStringSet F := The set of all of the strings that have an occurrence as the name of a free variable in the formula F.
-/
def Formula.freeStringSet (F : Formula) : Finset String :=
  F.varSet.biUnion Var.freeStringSet

/--
  Helper function for Formula.boundNatSet
-/
def Var.boundNatSet : Var → Finset ℕ
  | free_ _ => ∅
  | bound_ i => {i}

/--
  Formula.boundNatSet F := The set of all of the natural numbers that have an occurrence as the de Bruijn index of a bound variable in the formula F.
-/
def Formula.boundNatSet (F : Formula) : Finset ℕ :=
  F.varSet.biUnion Var.boundNatSet


--------------------------------------------------


/--
  Formula.closed F := True if and only if the formula F contains no free variables.
-/
def Formula.closed (F : Formula) : Prop :=
  F.freeVarSet = ∅


--------------------------------------------------


theorem occursIn_iff_mem_varSet
  (v : Var)
  (F : Formula) :
  occursIn v F ↔ v ∈ F.varSet :=
  by
  induction F
  case pred_ X vs =>
    simp only [occursIn]
    simp only [varSet]
    simp only [List.mem_toFinset]
  case not_ phi phi_ih =>
    simp only [occursIn]
    simp only [varSet]
    exact phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [occursIn]
    simp only [varSet]
    simp only [Finset.mem_union]
    congr!
  case forall_ _ phi phi_ih =>
    simp only [occursIn]
    simp only [varSet]
    exact phi_ih


theorem var_is_free_in_iff_mem_free_var_set
  (v : Var)
  (F : Formula) :
  occursIn v F ∧ v.isFree ↔ v ∈ F.freeVarSet :=
  by
  induction F
  case pred_ X vs =>
    simp only [Formula.freeVarSet]
    simp only [occursIn]
    simp only [Finset.mem_biUnion, List.mem_toFinset]
    constructor
    · intro a1
      obtain ⟨a1_left, a1_right⟩ := a1
      apply Exists.intro v
      cases v
      case free_ x =>
        simp only [Var.freeVarSet]
        constructor
        · exact a1_left
        · simp only [Finset.mem_singleton]
      case bound_ i =>
        contradiction
    · intro a1
      obtain ⟨u, ⟨a1_left, a1_right⟩⟩ := a1
      cases u
      case free_ x =>
        simp only [Var.freeVarSet] at a1_right
        simp only [Finset.mem_singleton] at a1_right
        rewrite [a1_right]
        constructor
        · exact a1_left
        · simp only [isFree]
      case bound_ i =>
        simp only [Var.freeVarSet] at a1_right
        simp only [Finset.notMem_empty] at a1_right
  case not_ phi phi_ih =>
    simp only [Formula.freeVarSet]
    simp only [occursIn]
    exact phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.freeVarSet]
    simp only [occursIn]
    simp only [Finset.mem_union]
    rewrite [← phi_ih]
    rewrite [← psi_ih]
    constructor
    · intro a1
      obtain ⟨a1_left, a1_right⟩ := a1
      cases a1_left
      case inl a1_left =>
        left
        exact ⟨a1_left, a1_right⟩
      case inr a1_left =>
        right
        exact ⟨a1_left, a1_right⟩
    · intro a1
      cases a1
      case inl a1 =>
        obtain ⟨a1_left, a1_right⟩ := a1
        constructor
        · left
          exact a1_left
        · exact a1_right
      case inr a1 =>
        obtain ⟨a1_left, a1_right⟩ := a1
        constructor
        · right
          exact a1_left
        · exact a1_right
  case forall_ _ phi phi_ih =>
    simp only [Formula.freeVarSet]
    simp only [occursIn]
    exact phi_ih


theorem isBoundIn_iff_mem_boundVarSet
  (v : Var)
  (F : Formula) :
  occursIn v F ∧ v.isBound ↔ v ∈ F.boundVarSet :=
  by
  induction F
  case pred_ X vs =>
    simp only [Formula.boundVarSet]
    simp only [occursIn]
    simp only [Finset.mem_biUnion, List.mem_toFinset]
    constructor
    · intro a1
      obtain ⟨a1_left, a1_right⟩ := a1

      apply Exists.intro v
      cases v
      case free_ x =>
        simp only [Var.isBound] at a1_right
      case bound_ i =>
        constructor
        · exact a1_left
        · simp only [Var.boundVarSet]
          simp only [Finset.mem_singleton]
    · intro a1
      obtain ⟨u, ⟨a1_left, a1_right⟩⟩ := a1
      cases u
      case free_ x =>
        simp only [Var.boundVarSet] at a1_right
        simp only [Finset.notMem_empty] at a1_right
      case bound_ i =>
        simp only [Var.boundVarSet] at a1_right
        simp only [Finset.mem_singleton] at a1_right
        rewrite [a1_right]
        constructor
        · exact a1_left
        · simp only [isBound]
  case not_ phi phi_ih =>
    simp only [Formula.boundVarSet]
    simp only [occursIn]
    exact phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.boundVarSet]
    simp only [occursIn]
    simp only [Finset.mem_union]
    rewrite [← phi_ih]
    rewrite [← psi_ih]
    constructor
    · intro a1
      obtain ⟨a1_left, a1_right⟩ := a1
      cases a1_left
      case inl a1_left =>
        left
        exact ⟨a1_left, a1_right⟩
      case inr a1_left =>
        right
        exact ⟨a1_left, a1_right⟩
    · intro a1
      cases a1
      case inl a1 =>
        obtain ⟨a1_left, a1_right⟩ := a1
        constructor
        · left
          exact a1_left
        · exact a1_right
      case inr a1 =>
        obtain ⟨a1_left, a1_right⟩ := a1
        constructor
        · right
          exact a1_left
        · exact a1_right
  case forall_ _ phi phi_ih =>
    simp only [Formula.boundVarSet]
    simp only [occursIn]
    exact phi_ih


theorem var_is_free_in_iff_mem_free_var_set'
  (v : Var)
  (F : Formula) :
  occursIn v F ∧ v.isFree ↔ v ∈ F.freeVarSet' :=
  by
  rewrite [occursIn_iff_mem_varSet]
  simp only [freeVarSet']
  simp only [Finset.mem_filter]


theorem isBoundIn_iff_mem_boundVarSet'
  (v : Var)
  (F : Formula) :
  occursIn v F ∧ v.isBound ↔ v ∈ F.boundVarSet' :=
  by
  rewrite [occursIn_iff_mem_varSet]
  simp only [boundVarSet']
  simp only [Finset.mem_filter]


--------------------------------------------------


lemma IsFreeIffExistsString
  (v : Var) :
  v.isFree ↔ ∃ (x : String), v = free_ x :=
  by
  cases v
  case free_ x =>
    constructor
    · intro a1
      apply Exists.intro x
      apply Eq.refl
    · intro a1
      simp only [isFree]
  case bound_ i =>
    constructor
    · intro a1
      simp only [isFree] at a1
    · intro a1
      obtain ⟨x, a1⟩ := a1
      contradiction


end LN


#lint
