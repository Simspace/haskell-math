----------------------------------------------------------------
-- 1. Statement
----------------------------------------------------------------

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
-- 2. Overview
----------------------------------------------------------------

-- Proof idea: given a subset S of the natural numbers and a
-- list L of distinct natural numbers, the number of elements
-- of L contained in S is bounded by the size of S.

-- Since the set {1, 2, ..., (L.length-1)} has size
-- (L.length-1), there must be some element of L which falls
-- outside of this range, and this is what we're looking for.

-- Structure of this file:
-- 1. (Above) A self-contained statement of the theorem.
-- 2. (Here) A tiny proof sketch.
-- 3. Counting elements in a list with a property.
-- 4. Counting and existence of list elements.
-- 5. Counting with different subsets.
-- 6. Bounded size subsets.
-- 7. Ranges.
-- 8. Main proof.

----------------------------------------------------------------
-- 3. Counting elements in a list with a property
----------------------------------------------------------------

-- Every fact involving natural numbers and lists that we care
-- about in this file (equality, order relation, list length,
-- membership testing) is decidable. In a sense this is great,
-- because more approaches are viable. But it's not clear from
-- the outset which of these approaches will be easier.
--
-- For example, how should we represent subsets of the natural
-- numbers?
--
-- * As Prop-valued predicates? This allows subsets whose
--   description is non-computable.
--
-- * As bool-valued predicates? This only allows subsets whose
--   description is computable.
--
-- * As a few custom types, for the few subsets we care about,
--   like consecutive ranges of natural numbers?
--
-- My experience so far is that custom types need a lot of glue
-- and boilerplate. Also, that bools make it easy to define
-- functions, but hard to prove things about them. So, I'm
-- defining subsets as Prop-valued predicates.
--
-- This is one of the ways provided by the core library,
-- incidentally:
example :
  (set nat) = (nat -> Prop)
  := rfl

-- Next, how should we talk about counting elements of a list
-- which belong to a given subset of the natural numbers?
--
-- * Using a function which takes a predicate and a list and
--   returns the count, as a natural number?
--
-- * Using a Prop which takes a predicate, a list, a count, and
--   states that the count is correct?
--
-- The function approach can work, because it can also take as
-- an extra parameter a proof that the given predicate is
-- decidable, even if it's a Prop-valued predicate. But again,
-- my experience is that functions are easy to define but hard
-- to use in proofs. So, I'm using a Prop for stating counts.
--
-- The order of arguments (subset, count, list) is a bit weird,
-- but it happened to make some of pattern matching easier.
inductive count (S : set nat) : nat -> (list nat) -> Prop
  -- The empty list has 0 elements in the subset S.
  | nil {} : (count 0 [])
  -- The case when the head of the list is in S.
  | cons_true : forall {head tail c},
      (head ∈ S) ->
      (count c tail) ->
      (count (c+1) (head :: tail))
  -- The case when the head of the list is not in S.
  | cons_false : forall {head tail c},
      (head ∉ S) ->
      (count c tail) ->
      (count c (head :: tail))

-- Given a subset S and a list L, the count is not guaranteed to
-- exist, because the predicate defining S may not be provably
-- true or false on an element of L.
-- But if the count does exist, it's unique.
lemma count_unique {S : set nat} : forall {c₁ c₂ : nat} {L : list nat},
  (count S c₁ L) ->
  (count S c₂ L) ->
  (c₁ = c₂)
    -- Case 1: the empty list always has a count of 0.
    | 0 0 []
      count.nil
      count.nil :=
        (eq.refl 0)
    -- Case 2: the head of the list is in S.
    | (c₁+1) (c₂+1) (head :: tail)
      (count.cons_true _ tail_count₁)
      (count.cons_true _ tail_count₂) :=
        (congr_arg nat.succ
          (count_unique tail_count₁ tail_count₂))
    -- Case 3: the two counts disagree on whether the head of
    -- the list is in S or not, which is a contradiction.
    | (c₁+1) c₂ (head :: tail)
      (count.cons_true head_in_S _)
      (count.cons_false head_notin_S _) :=
        (absurd head_in_S head_notin_S)
    -- Case 4: symmetric to case 3, also absurd.
    | c₁ (c₂+1) (head :: tail)
      (count.cons_false head_notin_S _)
      (count.cons_true head_in_S _) :=
        (absurd head_in_S head_notin_S)
    -- Case 5: the head of the list is not in S.
    | c₁ c₂ (head :: tail)
      (count.cons_false _ tail_count₁)
      (count.cons_false _ tail_count₂) :=
        (count_unique tail_count₁ tail_count₂)
    -- Cases 6, 7, 8, 9: automatically proved to be impossible.

-- For decidable predicates, the count does exist.
lemma count_decidable (S : set nat) [decidable_pred S] :
  forall (L : list nat),
  exists (c : nat), (count S c L)
    | [] := ⟨0, count.nil⟩
    | (head :: tail) :=
      let ⟨c, tail_count⟩ := (count_decidable tail)
      in if h : (S head)
      then ⟨c+1, count.cons_true h tail_count⟩
      else ⟨c, count.cons_false h tail_count⟩

----------------------------------------------------------------
-- 4. Counting and existence of list elements
----------------------------------------------------------------

-- Here are four lemmas that relate the counting of elements in
-- a list, and the existence of elements) in the list. They
-- provide the glue needed to connect the theorem statement at
-- the top of the file with the machinery used in the proof.

-- If the count is zero, then no element of the list is in the
-- subset. (This lemma is not actually used, but it just fits in
-- with the rest of the section.)
lemma count_zero {S : set nat} : forall {L : list nat},
  (count S 0 L) ->
  (forall (n : nat), (n ∈ L) -> (n ∈ S) -> false)
    | [] _
      _ n_in_L _ :=
        (list.not_mem_nil _ n_in_L)
    | (head :: tail) (count.cons_false head_notin_S tail_count)
      n n_in_L n_in_S :=
        (or.elim
          (list.eq_or_mem_of_mem_cons n_in_L)
          -- Derive a contradiction from (n = head).
          (fun n_eq_head,
            head_notin_S (eq.rec n_in_S n_eq_head))
          -- Derive a contradiction from (n ∈ tail).
          (fun n_in_tail,
            count_zero tail_count n n_in_tail n_in_S))

-- If the count is positive, then some element of the list is in
-- the subset. (The conclusion is written in just the right form
-- for the theorem statement at the top of the file.)
lemma count_positive {S : set nat} {c : nat} : forall {L : list nat},
  (count S (c+1) L) ->
  (exists (n : nat), (n ∈ L) ∧ (n ∈ S))
    -- The n we're looking for is the head.
    | (head :: tail) (count.cons_true head_in_S _) :=
      ⟨head, list.mem_cons_self _ _, head_in_S⟩
    -- The n we're looking for is in the tail.
    | (head :: tail) (count.cons_false _ tail_count) :=
      -- We have to re-wrap the recursive result for the tail
      -- so that it applies to (head :: tail).
      (@exists_imp_exists _
        (fun n, (n ∈ tail) ∧ (n ∈ S))
        (fun n, (n ∈ (head :: tail)) ∧ (n ∈ S))
        (fun n, and_implies (list.mem_cons_of_mem _) id)
        -- The recursive result.
        (count_positive tail_count))

-- The previous two lemmas are about going from a counting fact
-- to an existence fact; the following three lemmas go the other
-- way, from a (non-)existence fact to a counting fact.

-- A non-element of the list has a count of 0.
lemma count_notin {n : nat} : forall {L : list nat},
  (n ∉ L) ->
  (count (eq n) 0 L)
    | [] _ := count.nil
    | (head :: tail) n_notin_L :=
      (count.cons_false
        -- Composition because of negation.
        (n_notin_L ∘ or.inl)
        (count_notin
          (n_notin_L ∘ or.inr)))

-- An element of a list of distinct elements has a count of 1.
lemma count_distinct {n : nat} : forall {L : list nat},
  L.distinct ->
  (n ∈ L) ->
  (count (eq n) 1 L)
    | [] _ n_in_L :=
      -- An absurd case, since n ∉ [].
      false.elim (list.not_mem_nil _ n_in_L)
    -- Pattern matching on the shape of L, and also on the proof
    -- of (n ∈ L), which can be either (n = head)...
    | (head :: tail) ⟨head_notin_tail, _⟩
      (or.inl n_eq_head) :=
        (count.cons_true
          n_eq_head
          (count_notin (eq.rec
            head_notin_tail
            n_eq_head.symm)))
    -- ...or (n ∈ tail).
    | (head :: tail) ⟨head_notin_tail, tail_distinct⟩
      (or.inr n_in_tail) :=
        (count.cons_false
          (fun n_eq_head,
            head_notin_tail (eq.rec
              n_in_tail
              n_eq_head))
          (count_distinct
            tail_distinct
            n_in_tail))

-- Because equality of natural numbers is decidable, the
-- condition (n ∈ L) is decidable, so we can package the
-- previous two lemmas into one: the count of any number in a
-- list with distinct elements is at most 1.
lemma count_distinct_le (n : nat) {L : list nat} :
  L.distinct ->
  exists (c : nat), (count (eq n) c L) ∧ (c ≤ 1) :=
    fun L_distinct, if h : (n ∈ L)
    then ⟨1, count_distinct L_distinct h, nat.le_refl _⟩
    else ⟨0, count_notin h, nat.zero_le _⟩

----------------------------------------------------------------
-- 5. Counting with different subsets
----------------------------------------------------------------

-- In the definition of "count" above, the subset predicate is
-- fixed, and the count is defined recursively on the list.

-- Another way of counting elements is to keep the list fixed,
-- but decompose the subset as a union of other subsets. This
-- section provides lemmas to deal with this.

-- The empty set always has a count of zero. (This is included
-- here because the empty set is the empty union.)
lemma count_empty_set : forall {L : list nat},
  (count ∅ 0 L)
    | [] := count.nil
    | (head :: tail) := (count.cons_false id count_empty_set)

-- For two subsets and a fixed list, the count of the union
-- is bounded by the sum of the counts.
--
-- This is used twice later:
--
-- * To split up the count of elements in L that are ≥L.length
--   from those that are <L.length; and
--
-- * To decompose the count of elements in {1, 2, 3, ..., m}
--   into the count for each of the singletons {1}, {2},
--   {3}, ..., {m}.
--
-- The proof idea is trivial, but the proof is very long,
-- because 4 of the 5 cases are almost-but-not-quite the same,
-- and I didn't figure out a simple way to factor out the
-- commonalities. Possibly I should have used tactics and/or
-- I have the wrong abstractions above.
lemma count_union {S₁ S₂ : set nat} :
  forall {c₁ c₂ : nat} {L : list nat},
  (count S₁ c₁ L) ->
  (count S₂ c₂ L) ->
  exists (c : nat), (count (S₁ ∪ S₂) c L) ∧ (c ≤ c₁ + c₂)
    | c₁ c₂ []
      count.nil
      count.nil :=
        ⟨0, count.nil, nat.zero_le 0⟩
    | (c₁+1) (c₂+1) (head :: tail)
      (count.cons_true head_in_S₁ tail_count₁)
      (count.cons_true head_in_S₂ tail_count₂) :=
        let ⟨c, tail_count, c_le_sum⟩ :=
          (count_union tail_count₁ tail_count₂)
        in ⟨c+1,
          (count.cons_true
            (or.inl head_in_S₁)
            tail_count),
          -- The "simp" tactic is used here to rewrite sums of
          -- natural numbers using commutativity and
          -- associativity, because that's just too tedious.
          by {simp, exact
            (nat.succ_le_succ
              (nat.le_succ_of_le
                c_le_sum))}⟩
    | (c₁+1) c₂ (head :: tail)
      (count.cons_true head_in_S₁ tail_count₁)
      (count.cons_false head_notin_S₂ tail_count₂) :=
        let ⟨c, tail_count, c_le_sum⟩ :=
          (count_union tail_count₁ tail_count₂)
        in ⟨c+1,
          (count.cons_true
            (or.inl head_in_S₁)
            tail_count),
          -- Another use to the "simp" tactic to avoid tedium.
          by {simp, exact
            (nat.succ_le_succ
              c_le_sum)}⟩
    | c₁ (c₂+1) (head :: tail)
      (count.cons_false head_notin_S₁ tail_count₁)
      (count.cons_true head_in_S₂ tail_count₂) :=
        let ⟨c, tail_count, c_le_sum⟩ :=
          (count_union tail_count₁ tail_count₂)
        in ⟨c+1,
          (count.cons_true
            (or.inr head_in_S₂)
            tail_count),
          -- No need for "simp" in this case, luckily.
          (nat.succ_le_succ c_le_sum)⟩
    | c₁ c₂ (head :: tail)
      (count.cons_false head_notin_S₁ tail_count₁)
      (count.cons_false head_notin_S₂ tail_count₂) :=
        let ⟨c, tail_count, c_le_sum⟩ :=
          (count_union tail_count₁ tail_count₂)
        in ⟨c,
          (count.cons_false
            (or.rec head_notin_S₁ head_notin_S₂)
            tail_count),
          c_le_sum⟩

----------------------------------------------------------------
-- 6. Bounded size subsets
----------------------------------------------------------------

-- This section is about subsets of the natural numbers formed
-- inductively by taking the empty set, and adding elements to
-- the subset one by one. Note that we don't check whether the
-- added element is already in the subset, so we only obtain an
-- upper bound on the size of the subset.

-- An inductive upper bound for the size of a subset.
inductive bounded : (set nat) -> nat -> Type
| nil : (bounded ∅ 0)
| cons : forall head tail s,
    (bounded tail s) ->
    (bounded (tail ∪ (eq head)) (s+1))

-- A version of the pigeonhole principle, for these inductively
-- constructed subsets of the natural numbers: a list of
-- distinct natural numbers cannot contain more elements in the
-- subset than the size bound of the subset.
-- This lemma also states that the count is computable for
-- subsets defined this way.
lemma count_bounded {L : list nat}
  (h : L.distinct) :
  forall {S : set nat} {s : nat}, (bounded S s) ->
  exists (c : nat), (count S c L) ∧ (c ≤ s)
    | _ _ bounded.nil := ⟨0, count_empty_set, nat.zero_le 0⟩
    | _ _ (bounded.cons head tail s tail_bounded) :=
      let
        ⟨c₁, tail_count, c₁_le_s⟩ :=
          (count_bounded tail_bounded),
        ⟨c₂, head_count, c₂_le_1⟩ :=
          (count_distinct_le head h),
        ⟨c, L_count, c_le_sum⟩ :=
          (count_union tail_count head_count)
      in ⟨c, L_count,
        (@nat.le_trans c (c₁ + c₂) (s+1)
          c_le_sum
          (add_le_add c₁_le_s c₂_le_1))⟩

----------------------------------------------------------------
-- 7. Ranges
----------------------------------------------------------------

-- The previous lemmas are written for more general subsets of
-- the natural numbers, but we only care about two kinds:
--
-- * Subsets of the form {1, 2, 3, ..., m}, which we'll call
--   "positive ranges"; and
--
-- * Subsets of the form {m+1, m+2, m+3, ...}, which we'll call
--   "positive rays".
--
-- We need lemmas about the size of positive ranges, and a few
-- ways to break down these subsets as unions of other subsets.

-- The subset {1, 2, 3, ..., m}.
def positive_range (m : nat) : (set nat) :=
  (fun n, (0 < n) ∧ (n ≤ m))

-- When m=0, this is the empty set.
lemma positive_range_zero :
  (positive_range 0) = ∅ :=
    funext (fun n, propext ⟨
      -- positive range ⊆ empty set
      (fun ⟨zero_lt_n, n_le_zero⟩,
        nat.lt_le_antisymm zero_lt_n n_le_zero),
      -- empty set ⊆ positive range
      false.elim⟩)

-- When m>0, it's a union of a smaller range and a singleton.
lemma positive_range_succ (m : nat) :
  (positive_range (m+1)) = (positive_range m) ∪ (eq (m+1)) :=
    funext (fun n, propext ⟨
      -- bigger range ⊆ union
      (fun ⟨zero_lt_n, n_le_succ_m⟩,
        (or.elim (nat.eq_or_lt_of_le n_le_succ_m))
          (fun (h : n = m+1), or.inr h.symm)
          (fun (h : n < m+1), or.inl
            ⟨zero_lt_n, (nat.le_of_lt_succ h)⟩)),
      -- union ⊆ bigger range
      (@or.rec
        -- condition for the first subset in the union
        ((0 < n) ∧ (n ≤ m))
        -- condition for the second subset in the union
        (m+1 = n)
        -- target condition, for the bigger range
        ((0 < n) ∧ (n ≤ m+1))
        -- smaller range ⊆ bigger range
        (fun ⟨zero_lt_n, n_le_m⟩, ⟨
          zero_lt_n,
          nat.le_succ_of_le n_le_m⟩)
        -- singleton ⊆ bigger range
        (fun h, ⟨
          eq.rec (nat.zero_lt_succ m) h,
          nat.le_of_eq h.symm⟩))⟩)

-- The subset {1, 2, 3, ..., m} has size m.
lemma positive_range_bounded : forall (m : nat),
  (bounded (positive_range m) m)
    | 0 := (eq.rec
      (bounded.nil)
      positive_range_zero.symm)
    | (m+1) := (eq.rec
      (bounded.cons _ _ _ (positive_range_bounded m))
      (positive_range_succ m).symm)

-- The infinite subset {m+1, m+2, m+3, ...}.
def positive_ray (m : nat) : (set nat) :=
  (fun n, m < n)

-- The predicate in the definition of positive_ray is decidable,
-- so the lemma count_decidable can be used. The following
-- declaration records this fact in a way that the automated
-- typeclass search can find.
instance {m : nat} : (decidable_pred (positive_ray m)) :=
  -- In fact, Lean already knows that this predicate is
  -- decidable, but written in a different way. We have to
  -- explicitly write the type in the right way to convince it.
  (fun n, (infer_instance : decidable (m < n)))

-- The subset {1, 2, 3, ...} of all positive natural numbers is
-- the union of the positive range {1, 2, 3, ..., m} and the
-- positive ray {m+1, m+2, m+3, ...}.
lemma positive_split (m : nat) :
  (positive_ray 0) = (positive_range m) ∪ (positive_ray m) :=
    funext (fun n, propext ⟨
      -- positive ⊆ union
      (fun (zero_lt_n : 0 < n), or.elim
        (nat.lt_or_ge m n)
        (fun (m_lt_n : m < n), or.inr m_lt_n)
        (fun (n_le_m : n ≤ m), or.inl ⟨zero_lt_n, n_le_m⟩)),
      -- union ⊆ positive
      (@or.rec
        ((0 < n) ∧ (n ≤ m))
        (m < n)
        (0 < n)
        -- range ⊆ positive
        and.left
        -- ray ⊆ positive
        (nat.lt_of_le_of_lt (nat.zero_le m)))⟩)

----------------------------------------------------------------
-- 8. Main proof
----------------------------------------------------------------

-- In a list of positive integers, the number of elements which
-- are positive is the length of the list. This is a trivial
-- statement, but it's written as a separate lemma because the
-- proof is by induction on the list.
lemma positive_count : forall {L : list nat},
  L.positive -> (count (positive_ray 0) (L.length) L)
    | [] _ := count.nil
    | (head :: tail) ⟨head_positive, tail_positive⟩ :=
      (count.cons_true
        head_positive
        (positive_count tail_positive))

-- The proof is split in two cases so that, in the main case,
-- we are dealing with a list which is nonempty-by-construction,
-- rather than just nonempty-by-proposition.
theorem proof : goal
  -- The empty list case.
  -- (false.elim) works on Prop's, but (list.empty) is a bool,
  -- so there's some glue involved in this case.
  | [] ⟨L_nonempty, _, _⟩ :=
    (false.elim (L_nonempty (eq.refl tt)))
  -- The nonempty list case.
  | (head :: tail) ⟨_, L_distinct, L_positive⟩ :=
    let
      -- The tail has length (L.length-1).
      m := tail.length,
      -- The number of list elements in {1, 2, ..., m}.
      -- This number is at most m.
      ⟨c₁, low_count, c₁_le_m⟩ :=
        (count_bounded L_distinct (positive_range_bounded m)),
      -- The number of list elements that are ≥ (L.length).
      -- This will be at least 1.
      ⟨c₂, high_count⟩ :=
        (count_decidable (positive_ray m) (head :: tail)),
      -- The sum of the two numbers above is at least
      -- (L.length).
      ⟨c, split_count, c_le_sum⟩ :=
        (count_union low_count high_count)
    in have h_ineq : ((m+1) ≤ (m + c₂)), from (calc
      -- We computed (L.length) in two ways, so the two answers
      -- are equal.
      m+1 = c       : (count_unique
                        (positive_count L_positive)
                        (eq.rec
                          split_count
                          (positive_split m).symm))
      ... ≤ c₁ + c₂ : c_le_sum
      ... ≤ m + c₂  : (nat.add_le_add_right c₁_le_m c₂)),
    -- It's a bit annoying to get the predecessor of a natural
    -- number, because the core library defines (0.pred = 0).
    have h_eq : (c₂.pred + 1 = c₂), from
      (nat.succ_pred_eq_of_pos
        (nat.le_of_add_le_add_left h_ineq)),
    -- Now that we know the count of elements in L which are
    -- ≥ (L.length) is positive, rewrite the conclusion in the
    -- same way as the original theorem statement.
    (count_positive (@eq.rec _ c₂ _ high_count _ h_eq.symm))
