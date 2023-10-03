function sorted(s : seq<int>) : bool {
  forall k1, k2 :: 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
}

// Ex1
method copy(a : array<int>, l : int, r : int) returns (ret : array<int>)
  requires 0 <= l < r <= a.Length 
  ensures ret[..] == a[l..r]
{
  var size := r - l;
  ret := new int[size];
  var aux := 0;
  while (aux < size)
    invariant 0 <= aux <= ret.Length
    invariant forall k :: 0 <= k < aux ==> a[l + k] == ret[k]
    decreases size - aux
  {
    ret[aux] := a[l + aux];
    aux := aux + 1;
  }
}

// Ex2
method mergeArr(a : array<int>, l : int, m : int, r : int) 
  requires 0 <= l < m < r <= a.Length  
  requires sorted(a[l..m]) && sorted(a[m..r])
  ensures sorted(a[l..r]) 
  ensures a[..l] == old(a[..l])
  ensures a[r..] == old(a[r..]) 
  modifies a 
{
  ghost var oldArray := old(a[..]);
  var arr1 := copy(a, l, m);
  var arr2 := copy(a, m, r);
  var i := 0;
  var j := 0;
  var cur := l;
  while (i < arr1.Length || j < arr2.Length)
    invariant 0 <= i <= arr1.Length
    invariant 0 <= j <= arr2.Length
    invariant l <= cur <= r
    invariant cur == l + i + j
    invariant sorted(arr1[..]) && sorted(arr2[..])
    invariant (i < arr1.Length && cur - 1 >= l) ==> a[cur - 1] <= arr1[i]
    invariant (j < arr2.Length && cur - 1 >= l) ==> a[cur - 1] <= arr2[j]
    invariant sorted(a[l..cur])
    invariant forall k :: 0 <= k < l ==> oldArray[k] == a[k]
    invariant forall k :: r <= k < a.Length ==> oldArray[k] == a[k]
    decreases r - cur
  {
    if (i < arr1.Length  && (j >= arr2.Length || arr1[i] <= arr2[j])) {
      a[cur] := arr1[i];
      i := i + 1;
    } else {
      a[cur] := arr2[j];
      j := j + 1;
    }
    cur := cur + 1;
  }
  // assert a[l..cur] == a[l..r] == a[l..l+i+j];
  // assert sorted(a[l..cur]); 
  // assert forall k1, k2 :: l <= k1 < k2 < l + i ==> a[k1] <= a[k2];
  // assert sorted(a[l..m]);
  // assert a[l + i..l + i + j] == a[m..cur];
  // assert sorted(a[m..r]);
}

// Ex3
// method sortAux(a: array<int>, l: int, r: int)
//   requires 0 <= l <= r <= a.Length
//   ensures sorted(a[l..r])
//   modifies a
//   decreases r - l
// {
//   if (r - l < 2) {
//     return;
//   }
//   var m := (l + r) / 2;
//   sortAux(a, l, m);
//   sortAux(a, m, r);
//   mergeArr(a, l, m, r);
// }

method sortAux(a: array<int>, l: int, r: int)
  requires 0 <= l <= r <= a.Length
  requires r - l == 1 ==> sorted(a[l..r])
  ensures sorted(a[l..r])
  modifies a
  decreases r - l
{
  if (r - l >= 2) {
    var m := l + (r - l) / 2;
    assert m - l == 1 ==> sorted(a[l..m]);
    assert r - m == 1 ==> sorted(a[m..r]);
    printArray(a, l, r);
    sortAux(a, l, m);
    sortAux(a, m, r);
    // if (r != a.Length) {
    mergeArr(a, l, m, r);
    assert sorted(a[l..m]);
    assert sorted(a[m..r]);
    // }
  }
}

method sort (a : array<int>) 
  ensures sorted(a[..])
  modifies a 
{
  sortAux(a, 0, a.Length);
}

method printArray(a: array<int>, l: int, r: int) {
  var i := l;
  while (i < r) {
    if (i <= a.Length - 1 && i >= 0) {
      print a[i], "\n";
    }
    i := i + 1;
  }
  print "Iteration end\n";
}

// method Main()
// {
//   var a: array<int> := new int[6];
//   a[0],a[1],a[2],a[3],a[4],a[5] := 1,4,5,2,6,10;
//   sort(a);
//   // mergeArr(a, 0, 3, 6);
//   // var i := 0;
//   // while (i < 6) {
//   //   print a[i];
//   //   i := i + 1;
//   // }
// }
