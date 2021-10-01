predicate sorted_seq(a: seq<int>) {
   forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate sorted_range(a: array<int>, from: nat, until: nat)
requires from <= until <= a.Length
reads a {
    forall i, j :: from <= i < j < until ==> a[i] <= a[j]
}

predicate permutation_range(a1: seq<int>, a2: seq<int>,
                            b: array<int>,
                            from: nat, until: nat, m: map<int, (bool, int)>)
requires from <= until <= b.Length
requires until - from == |a1| + |a2|
requires |m| == |a1| + |a2|
requires bijection(m)
requires forall i :: from <= i < until ==> i in m
requires forall i :: from <= i < until ==>
  match m[i]
    case (true, n) => 0 <= n < |a1|
    case (false, n) => 0 <= n < |a2|
reads b {
    forall i :: from <= i < until ==>
      match m[i]
        case (true, n) => a1[n] == b[i]
        case (false, n) => a2[n] == b[i]
}

predicate sorted(a: array<int>) reads a {
  sorted_range(a, 0, a.Length)
}

predicate bijection(m: map<int, (bool, int)>) {
  var lvalues := set k | k in m && match m[k] case (left, _) => left == true
  :: match m[k] case (_, x) => x;
  var rvalues := set k | k in m && match m[k] case (left, _) => left == false
  :: match m[k] case (_, x) => x;

  var keys := set k | 0 <= k <= |m| :: k;

  keys == lvalues + rvalues
}

predicate permutation(a1: seq<int>,
                      a2: seq<int>,
                      b: array<int>,
                      m: map<int, (bool, int)>)
requires |a1| + |a2| == b.Length
requires |m| == |a1| + |a2|
requires bijection(m)
requires forall i :: 0 <= i < b.Length ==> i in m
requires forall i :: 0 <= i < b.Length ==>
  match m[i]
    case (true, n) => 0 <= n < |a1|
    case (false, n) => 0 <= n < |a2|
reads b {
  permutation_range(a1, a2, b, 0, b.Length, m)
}

// This function is *cursed*
method copy(a: seq<int>, c: array<int>, at: nat)
requires at <= c.Length
requires |a| == c.Length - at
ensures forall i :: 0 <= i < |a| ==> c[at + i] == a[i]
modifies c {
  var i := 0;
  while (i < |a|)
  decreases |a| - i
  invariant 0 <= i <= |a|
  invariant forall j :: 0 <= j < i ==> c[at + j] == a[j] {
    c[at + i] := a[i];
    i := i + 1;
  }
}

method merge(a1: seq<int>, a2: seq<int>)
    returns (res:array<int>, m: map<int, (bool, int)>)
    requires sorted_seq(a1)
    requires sorted_seq(a2)
    ensures sorted(res)
    ensures permutation(a1, a2, res, m)
    ensures res.Length == |a1| + |a2| {
  if(|a1| == 0 && |a2| == 0) {
    res := new int[0];
    m := map[];
    return;
  } else if (|a1| == 0) { // res := a2
    res := new int[|a2|];
    m := map i | 0 <= i < |a2| :: (false, i);
    assert(bijection(m));
    copy(a2, res, 0);
    assert(forall i :: 0 <= i < |a2| ==> res[i] == a2[i]);
    assert(permutation(a1, a2, res, m));
    assert(sorted(res));
    return;
  } else if (|a2| == 0) { // res := a1
    res := new int[|a1|];
    m := map i | 0 <= i < |a1| :: (true, i);
    assert(bijection(m));
    copy(a1, res, 0);
    assert(forall i :: 0 <= i < |a1| ==> res[i] == a1[i]);
    assert(permutation(a1, a2, res, m));
    assert(sorted(res));
    return;
  }

  // |a1| > 0 && |a2| > 0
  res := new int[|a1| + |a2|];
  var l := 0;
  var r := 0;
  var i := 0;

  // new index -> (old index, is_left)
  m := map[];

  while (i < res.Length)
  decreases res.Length - i
  invariant 0 <= l <= |a1|
  invariant 0 <= r <= |a2|
  invariant i == l + r
  invariant sorted_range(res, 0, i)
  invariant forall p, q :: 0 <= p < i && l <= q < |a1| ==> res[p] <= a1[q]
  invariant forall p, q :: 0 <= p < i && r <= q < |a2| ==> res[p] <= a2[q]
  invariant bijection(m)
  invariant permutation_range(a1[..l], a2[..r], res, 0, i, m) {
      if(l == |a1|) {
        res[i] := a2[r];
        r := r + 1;
        m := m[i := (false, r)];
      } else if (r == |a2|) {
        res[i] := a1[l];
        l := l + 1;
        m := m[i := (true, l)];
      } else if (a1[l] <= a2[r]) {
        res[i] := a1[l];
        l := l + 1;
        m := m[i := (true, l)];
      } else {
        res[i] := a2[r];
        r := r + 1;
        m := m[i := (false, r)];
      }
      i := i + 1;
  }
}
