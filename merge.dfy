predicate sorted_seq(a: seq<int>) {
   forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate sorted_until(a: array<int>, until: nat)
requires until <= a.Length
reads a {
    until == 0 ||
    forall i, j :: 0 <= i < j < until ==> a[i] <= a[j]
}

predicate permutation_until(a: seq<int>, b: array<int>, until: nat)
requires until <= b.Length
reads b {
    until == 0 ||
    (until == |a| &&
        forall i :: 0 <= i < until ==> b[i] in a)
}

predicate sorted(a: array<int>) reads a {
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

predicate permutation(a: seq<int>, b: array<int>) reads b {
    |a| == b.Length && forall i :: 0 <= i < b.Length ==> b[i] in a
}

predicate xor(a: bool, b: bool) {
    (a == true && b == false) || (a == false && b == true)
}

method merge(a1: seq<int>, a2: seq<int>) returns (res:array<int>)
    requires sorted_seq(a1)
    requires sorted_seq(a2)
    ensures sorted(res)
    ensures permutation(a1 + a2, res) {
  if(|a1| == 0 && |a2| == 0) {
    res := new int[0];
    return;
  } else if (|a1| == 0) {
    res := new int[|a2|];
    forall i | 0 <= i < |a2| { res[i] := a2[i]; }
    return;
  } else if (|a2| == 0) {
    res := new int[|a1|];
    forall i | 0 <= i < |a1| { res[i] := a1[i]; }
    return;
  }
  // Now both combined
  res := new int[|a1| + |a2|];
  var l := 0;
  var r := 0;
  var i := 0;

  while (l < |a1| && r < |a2|)
  decreases res.Length - i
  invariant 0 <= l <= |a1|
  invariant 0 <= r <= |a2|
  invariant i == l + r
  invariant sorted_until(res, i)
  invariant permutation_until(a1[..l] + a2[..r], res, i) {
      assert(forall j:: 0 <= j < i ==> sorted_until(res, j));
      if(a1[l] < a2[r]) {
        res[i] := a1[l];
        l := l + 1;
      } else {
        res[i] := a2[r];
        r := r + 1;
      }
      i := i + 1;
  }

  // only one of the two is true
  assert(xor(l == |a1|, r == |a2|));
  assert(i == l + r);

  if(l == |a1|) {
    forall j | r <= j < |a2| { res[i+j] := a2[j]; }
    return;
  }
  else if(r == |a2|) {
    forall j | l <= j < |a1| { res[i+j] := a1[j]; }
    return;
  }
}
