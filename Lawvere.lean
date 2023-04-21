import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Closed.Monoidal

def icongruent [CategoryTheory.Category α] {A B C : α}  (i : B ⟶ C) (f : A ⟶ B) (g : A ⟶ B) := f ≫ i = g ≫ i

noncomputable instance cartesian [CategoryTheory.Category α] [CategoryTheory.Limits.HasFiniteProducts α] : CategoryTheory.MonoidalCategory α where
  tensorObj x y := CategoryTheory.Limits.prod x y
  tensorUnit' := CategoryTheory.Limits.terminal α
  tensorHom := by
    intros X Y Z W f g
    simp
    exact CategoryTheory.Limits.prod.lift (CategoryTheory.Limits.prod.fst ≫ f) (CategoryTheory.Limits.prod.snd ≫ g)
  rightUnitor X := CategoryTheory.Limits.prod.rightUnitor X
  leftUnitor X := CategoryTheory.Limits.prod.leftUnitor X
  associator X Y Z := CategoryTheory.Limits.prod.associator X Y Z

structure interpreter [CategoryTheory.Category α] [CategoryTheory.Limits.HasFiniteProducts α] [inst: CategoryTheory.MonoidalClosed α] 
  (A E Y : α) (i : E ⟶ Y)  where
  map : A ⟶ (A ⟶[α] E)
  interprets : ∀f : A ⟶ E, ∃c : cartesian.tensorUnit' ⟶ A, 
    have lhs := CategoryTheory.MonoidalClosed.uncurry (c ≫  map) ≫ i
    have rhs := (cartesian.rightUnitor A).hom ≫ f ≫ i
    lhs = rhs
