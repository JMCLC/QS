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
// method mergeArr(a : array<int>, l : int, m : int, r : int) 
//   requires 0 <= l < m < r <= a.Length  
//   // requires sorted(a[l..m]) && sorted(a[m..r])
//   // ensures sorted(a[l..r]) 
//   ensures a[..l] == old(a[..l])
//   ensures a[r..] == old(a[r..]) 
//   modifies a 
// {
//   ghost var oldArray := old(a[..]);
//   var arr1 := copy(a, l, m);
//   var arr2 := copy(a, m, r);
//   var i := 0;
//   var j := 0;
//   var cur := l;
//   while (cur < r && i < arr1.Length && j < arr2.Length)
//     invariant 0 <= i <= arr1.Length
//     invariant 0 <= j <= arr2.Length
//     invariant l <= cur <= r
//     invariant forall k1, k2 :: l <= k1 < k2 < cur <= r ==> a[k1] <= a[k2]
//     invariant forall k :: 0 <= k < l ==> oldArray[k] == a[k]
//     invariant forall k :: r <= k < a.Length ==> oldArray[k] == a[k]
//     decreases r - cur
//   {
//     if (arr1[i] <= arr2[j]) {
//       a[cur] := arr1[i];
//       i := i + 1;
//     } else {
//       a[cur] := arr2[j];
//       j := j + 1;
//     }
//     cur := cur + 1;
//   }
// }

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
  while (i < arr1.Length && j < arr2.Length)
    invariant 0 <= i <= arr1.Length
    invariant 0 <= j <= arr2.Length
    invariant l <= cur <= r
    invariant sorted(a[l..cur]) && a[cur - 1] <= a[cur]
    invariant forall k :: 0 <= k < l ==> oldArray[k] == a[k]
    invariant forall k :: r <= k < a.Length ==> oldArray[k] == a[k]
    decreases r - cur
  {
    if (arr1[i] <= arr2[j]) {
      a[cur] := arr1[i];
      i := i + 1;
    } else {
      a[cur] := arr2[j];
      j := j + 1;
    }
    cur := cur + 1;
  }
}


// // Ex3
// method sort (a : array<int>) 
//   ensures sorted(a[..])
//   modifies a 
// {
//   // ToDo
// }





