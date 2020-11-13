Inductive binob : Set :=
  | C : binob
  | T : binob -> binob
  | M : binob -> binob -> binob.

Fixpoint isc (b : binob) :=
  match b with
  | C => C
  | T b' => T C
  | M b1 b2 => T C
  end.

Fixpoint identical (b : binob) :=
  match b with
  | C => C
  | T b' => T (identical b')
  | M b1 b2 => M (identical b1) (identical b2)
  end.

Theorem identical_b_b : forall (b : binob), identical b = b.
  induction b.
  reflexivity.
  simpl; rewrite IHb; reflexivity.
  simpl; rewrite IHb1; rewrite IHb2; reflexivity.
  Defined.

(* boolean embedding *)
Fixpoint binob_to_bool (b : binob) :=
  match b with
  | C => false
  | T b' => negb (binob_to_bool b')
  | M b1 b2 => andb (binob_to_bool b1) (binob_to_bool b2)
  end.

Check binob_to_bool.

Fixpoint binob_to_nat (b : binob) :=
  match b with
  | C => 0
  | T b' => S (binob_to_nat b')
  | M b1 b2 => (binob_to_nat b1) * (binob_to_nat b2)
  end.


