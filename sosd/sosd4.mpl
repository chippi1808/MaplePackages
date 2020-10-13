#Source: https://t-t-h-n-e-w.blogspot.com/2020/10/sos-program-cho-inequality-in-1-var.html
sosd4:=proc(expr,x)
	local F,f,sol;
	f:=a*x^3+x^4+b*x^2+c*x+d;
	F := (x^2+(1/2)*a*x+n)^2-(1/4)*(a^2*x+2*a*n-4*b*x+8*n*x-2*c)^2/(a^2-4*b+8*n)+(a^2*d-2*a*c*n+4*b*n^2-8*n^3-4*b*d+c^2+8*d*n)/(a^2-4*b+8*n);
	sol:=solve(identity(f=expr, x), {a, b, c,d});
	subs(sol,{b-2*n-(1/4)*a^2 >= 0, a^2*d-2*a*c*n+4*b*n^2-8*n^3-4*b*d+c^2+8*d*n <= 0});
	print(evalf(solve(%)));
	F:=subs(sol,F);
	print(F);
end:
