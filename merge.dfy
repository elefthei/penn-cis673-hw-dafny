predicate sorted_seq(a: seq<int>) {
   forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate sorted_range(a: array<int>, from: nat, until: nat)
requires from <= until <= a.Length
reads a {
    forall i, j :: from <= i < j < until ==> a[i] <= a[j]
}

predicate permutation_range(a: seq<int>, b: array<int>, from: nat, until: nat)
requires from <= until <= b.Length
requires until - from == |a|
reads b {
    var bs := b[from .. until];
    forall i :: from <= i < |bs| ==> b[i] in a &&
    forall i :: from <= i < |a| ==> a[i] in bs
}

predicate sorted(a: array<int>) reads a {
  sorted_range(a, 0, a.Length)
}

predicate permutation(a: seq<int>, b: array<int>)
requires |a| == b.Length
reads b {
  permutation_range(a, b, 0, b.Length)
}

method tester()  {
  var a : seq<int> := [1, 2, 3, 4][..];
  assert(|a[..0]| == 0);
}

method copy(a: seq<int>, c: array<int>, at: nat)
requires at <= c.Length
requires |a| == c.Length - at
ensures forall i :: 0 <= i < |a| ==> c[at + i] == a[i]
modifies c {
  var i := 0;
  while (i < |a|)
  decreases |a| - i
  invariant 0 <= i <= |a|
  invariant forall j :: 0 <= j < i ==> c[at + j] == a[j]
  {
    c[at + i] := a[i];
    i := i + 1;
  }
}

method merge(a1: seq<int>, a2: seq<int>) returns (res:array<int>)
    requires sorted_seq(a1)
    requires sorted_seq(a2)
    ensures sorted(res)
    ensures res.Length == |a1| + |a2|
    ensures permutation(a1 + a2, res) {
  if(|a1| == 0 && |a2| == 0) {
    res := new int[0];
    return;
  } else if (|a1| == 0) { // res := a2
    res := new int[|a2|];
    copy(a2, res, 0);
    assert(forall i :: 0 <= i < |a2| ==> res[i] == a2[i]);
    assert(permutation(a2, res));
    assert(sorted(res));
    return;
  } else if (|a2| == 0) { // res := a1
    res := new int[|a1|];
    copy(a1, res, 0);
    assert(forall i :: 0 <= i < |a1| ==> res[i] == a1[i]);
    assert(permutation(a1, res));
    assert(sorted(res));
    return;
  }

  // |a1| > 0 && |a2| > 0
  res := new int[|a1| + |a2|];
  var l := 0;
  var r := 0;
  var i := 0;

  while (l < |a1| && r < |a2|)
  decreases res.Length - i
  invariant 0 <= l <= |a1|
  invariant 0 <= r <= |a2|
  invariant i == l + r
  invariant sorted_range(res, 0, i)
  invariant forall p, q :: 0 <= p < i && l <= q < |a1| ==> res[p] <= a1[q]
  invariant forall p, q :: 0 <= p < i && r <= q < |a2| ==> res[p] <= a2[q]
  invariant permutation_range(a1[..l] + a2[..r], res, 0, i) {
      if(a1[l] <= a2[r]) {
        res[i] := a1[l];
        l := l + 1;
        assert(permutation_range(a1[..l] + a2[..r], res, 0, i));
      } else {
        res[i] := a2[r];
        r := r + 1;
      }
      i := i + 1;
  }

  // one of the two is true
  assert(l == |a1| || r == |a2|);

  if(l == |a1|) {
    var ra2 := a2[r..];
    copy(ra2, res, i);
    assert(i == |a1| + r);
    assert(res.Length == |a1| + |a2|);
    assert(forall j :: 0 <= j < |ra2| ==> res[i + j] == ra2[j]);
    assert(forall j :: r <= j < |a2| ==> res[i+j] == a2[j]);
    assert(sorted_seq(ra2));
    assert(sorted(res));
    return;
  } else if(r == |a2|) {
    assert(i == l + |a2|);
    assert(res.Length == |a1| + |a2|);
    copy(a1[l..], res, i);
    return;
  }
}
