Lemma not_iff : forall p q, p <-> q -> ~ p <-> ~ q.
Proof.
  intros.
  destruct H.
  split.
  - intro. intro. apply H0 in H2. contradiction.
  - intro. intro. apply H in H2. contradiction.
  Qed.
