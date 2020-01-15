-- Every nonempty list of distinct strictly positive integers
-- has a member at least as large as the length of the list.

----------------------------------------------------------------

-- The proposition that a list has distinct elements.
def list.distinct : list nat -> Prop
  | [] := true
  | (head :: tail) := (head ∉ tail) ∧ tail.distinct

-- The proposition that a list only has positive elements.
def list.positive : list nat -> Prop
  | [] := true
  | (head :: tail) := (head > 0) ∧ tail.positive

-- The theorem statement.
def goal : Prop := forall (L : list nat),
  ¬L.empty ∧ L.distinct ∧ L.positive ->
  exists (n : nat), (n ∈ L) ∧ (n ≥ L.length)

----------------------------------------------------------------

inductive chain : nat -> nat -> Type
  | nil : chain 0 0
  | cons : forall {a b len : nat},
      (a > b) -> (chain b len) -> (chain a (len+1))
namespace chain
  lemma max_ge_len : forall {a len}, (chain a len) -> (a ≥ len)
    | _ _ nil := (nat.less_than_or_equal.refl 0)
    | a _ (cons h tail) := (nat.lt_of_le_of_lt (max_ge_len tail) h)

  def member (n : nat) : forall {a len}, (chain a len) -> Prop
    | _ _ nil := false
    | a _ (cons _ tail) := (n = a) ∨ (member tail)
  instance {a len} : has_mem nat (chain a len) := ⟨fun n C, member n C⟩

  lemma max_ge_mem {n : nat} : forall {a len} {C : chain a len}, (n ∈ C) -> (a ≥ n)
    | _ _ nil := false.elim
    | a _ (@cons _ b _ a_gt_b C) := (or.rec nat.le_of_eq
      (fun h, nat.le_trans (max_ge_mem h) (nat.le_of_lt a_gt_b)))
end chain

----------------------------------------------------------------

def insertion_helper (head : nat) :
  forall {a len} (C : chain a len),
    (head ∉ C) ∧ (head > 0) -> 
      Σ' {a'} (C' : chain a' (len+1)),
        (forall (n : nat), (n ∈ C') ↔ ((n = head) ∨ (n ∈ C)))
| _ _ chain.nil ⟨_, h_positive⟩ :=
  ⟨_, (chain.cons h_positive chain.nil), (fun n, iff.refl _)⟩
| a (len+1) (@chain.cons _ b _ a_gt_b C) ⟨h_nonmember, h_positive⟩ :=
  if head_vs_a : head > a
  then ⟨_, (chain.cons head_vs_a (chain.cons a_gt_b C)),
    (fun n, iff.refl _)⟩
  else let
    a_gt_head : a > head :=
      (or.resolve_right (nat.lt_trichotomy head a)
        (or.rec (h_nonmember ∘ or.inl) head_vs_a)),
    ⟨b', C', head_or_C⟩ :=
      insertion_helper C ⟨h_nonmember ∘ or.inr, h_positive⟩,
    a_gt_b' : a > b' :=
      (or.rec_on ((head_or_C b').mp (let (chain.cons _ _) := C' in or.inl rfl))
        (fun (h : b' = head), eq.substr h a_gt_head)
        (fun (h : b' ∈ C), nat.lt_of_le_of_lt (chain.max_ge_mem h) a_gt_b))
  in ⟨_, (chain.cons (a_gt_b') C'),
    (fun n, iff.intro
      (or.rec
        (or.inr ∘ or.inl)
        ((or.imp_right or.inr) ∘ (head_or_C n).mp))
      (or.rec
        (or.inr ∘ (head_or_C n).mpr ∘ or.inl)
        (or.imp_right ((head_or_C n).mpr ∘ or.inr))))⟩

def insertion_sort :
  forall (L : list nat), L.distinct ∧ L.positive ->
    Σ' (a : nat) (C : chain a L.length),
      (forall (n : nat), (n ∈ C) ↔ (n ∈ L))
| [] _ := ⟨0, chain.nil, (fun n, iff.refl _)⟩
| (head :: tail) ⟨h_distinct, h_positive⟩ :=
  let
    ⟨_, C, h_permuted⟩ := insertion_sort tail
      ⟨h_distinct.right, h_positive.right⟩,
    ⟨_, C', head_or_C⟩ := insertion_helper head C
      ⟨(h_distinct.left ∘ (h_permuted head).mp), h_positive.left⟩
  in ⟨_, C',
    (fun n, iff.intro
      ((or.imp_right (h_permuted n).mp) ∘ (head_or_C n).mp)
      ((head_or_C n).mpr ∘ (or.imp_right (h_permuted n).mpr)))⟩

----------------------------------------------------------------

theorem proof : goal
| [] ⟨h, _⟩ := false.elim (h rfl)
| (head :: tail) ⟨_, h⟩ :=
  let ⟨a, C, h_permuted⟩ := insertion_sort (head :: tail) h
  in ⟨a,
    ((h_permuted a).mp (let (chain.cons _ _) := C in or.inl rfl)),
    (chain.max_ge_len C)⟩
