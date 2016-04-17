and 1235456 321.12  0.12345 12
Var
  i,k,ans:longint;
  max,n,m:int64;

  flag,v:array[0..33]of int64;


Procedure dfs(now,st:int64);
  var
    i:longint;
  begin
    if now>ans then ans:=now;
    if (st>n) then exit;
    if now+(n-st+1)*max<ans then exit;

    for i:=1 to n do
      if (flag[i]=0)and(now+v[i]<=m) then
         begin
           flag[i]:=1;
           dfs(now+v[i],st+1);
           flag[i]:=0;
         end;
  end;
Begin
  while not eof do
    begin
      fillchar(flag,sizeof(flag),0);
      max:=0;
      readln(n,m);
      for i:=1 to n do
        begin
          read(v[i]);
          if v[i]>max then max:=v[i];
        end;
      ans:=0;
      dfs(0,1);
      writeln(ans);
    end;
End.
SSS