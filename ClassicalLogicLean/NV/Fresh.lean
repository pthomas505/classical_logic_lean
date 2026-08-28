import ClassicalLogicLean.NV.Formula

import Mathlib.Tactic
import Mathlib.Data.String.Lemmas


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


/--
  `finset_var_name_max_len css` := The length of the longest variable name in the finite set of variable names `css` or 0 if the set is empty.
-/
def finset_var_name_max_len :
  Finset VarName_ → ℕ :=
  Finset.fold (fun (m n : ℕ) => max m n) 0 (fun (x : VarName_) => x.length)


theorem finset_var_name_max_len_mem
  (cs : VarName_)
  (css : Finset VarName_)
  (h1 : cs ∈ css) :
  cs.length ≤ finset_var_name_max_len css :=
  by
    induction css using Finset.induction_on
    case empty =>
      simp only [Finset.notMem_empty] at h1
    case insert hd tl ih_1 ih_2 =>
      simp only [Finset.mem_insert] at h1

      cases h1
      case inl h1 =>
        rewrite [h1]
        unfold finset_var_name_max_len
        simp only [Finset.fold_insert_idem, le_sup_left]
      case inr h1 =>
        simp only [finset_var_name_max_len] at ih_2

        simp only [finset_var_name_max_len]
        simp only [Finset.fold_insert_idem, le_sup_iff]
        right
        apply ih_2
        exact h1


/--
  `fresh cs c css` := If the variable name `cs` is not a member of the finite set of variable names `css` then `cs` is returned. If `cs` is a member of `css` then the character `c` is repeatedly appended to `cs` until the resulting variable name is not a member of `css`. The resulting variable name is then returned.
-/
def fresh
  (cs : VarName_)
  (c : Char)
  (css : Finset VarName_) :
  VarName_ :=
  if h : cs ∈ css
  then
    have : (finset_var_name_max_len css) - cs.length < (finset_var_name_max_len css) + 1 - cs.length :=
    by
      apply Nat.sub_lt_sub_right
      · apply finset_var_name_max_len_mem
        exact h
      · apply lt_add_one
  fresh (VarName_.mk (cs.toString ++ c.toString)) c css
  else cs
  termination_by (finset_var_name_max_len css) + 1 - cs.length


theorem fresh_not_mem
  (cs : VarName_)
  (c : Char)
  (css : Finset VarName_) :
  fresh cs c css ∉ css :=
  if h : cs ∈ css
  then
    have : (finset_var_name_max_len css) - cs.length < (finset_var_name_max_len css) + 1 - cs.length :=
    by
      apply Nat.sub_lt_sub_right
      · apply finset_var_name_max_len_mem
        exact h
      · apply lt_add_one
  by
    unfold fresh
    split
    case isTrue c1 =>
      apply fresh_not_mem
    case isFalse c1 =>
      contradiction
  else by
    unfold fresh
    split
    case isTrue c1 =>
      contradiction
    case isFalse c1 =>
      exact h
  termination_by (finset_var_name_max_len css) + 1 - cs.length
