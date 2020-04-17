#include <iostream>
#include <algorithm>
#include <vector>
#include <bitset>
#include <numeric>
#include <map>
#include <set>
#include <assert.h>
#include <random>
#include <iomanip>
#include <random>
#include <iomanip>
#include <fstream>

using namespace std;

typedef vector<vector<double> > matrix;
typedef vector<double> row;

matrix inv(matrix mat)
{
    double temp;
    int n = mat.size();
    for (int i = 0; i < n; i++)
    {
        mat[i].resize(n * 2);
        for (int j = 0; j < 2 * n; j++)
        {
            if (j == (i + n))
                mat[i][j] = 1;
        }
    }

    for (int i = 0; i < n; i++)
    {
        int I=i;
        for (int j=i+1; j<n; j++)
        {
            if (abs(mat[j][i])>abs(mat[I][i]))
            {
                I=j;
            }
        }
        swap(mat[i],mat[I]);
        if (abs(mat[i][i])<1e-13)
        {
            throw new invalid_argument ("degenerate matrixxx");
        }
        for (int j = 0; j < n; j++)
        {
            if (j != i)
            {
                temp = mat[j][i] / mat[i][i];
                for (int k = 0; k < 2 * n; k++)
                {
                    mat[j][k] -= mat[i][k] * temp;
                }
            }
        }
    }
    for (int i = 0; i < n; i++)
    {
        temp = 1.0 / mat[i][i];
        for (int j = 0; j < 2 * n; j++)
        {
            mat[i][j] *= temp;
        }
    }



    for (int i=0; i<n; i++)
    {
        for (int j=0; j<n; j++)
            mat[i][j]=mat[i][j+n];
        mat[i].resize(n);
    }


    return mat;
}

matrix Z(int n)
{
    return matrix(n,row(n,0));
}

matrix E(int n)
{
    matrix m=Z(n);
    for (int i=0; i<n; i++)
        m[i][i]=1;
    return m;
}



matrix mul(matrix& a,matrix b)
{
    assert(a[0].size()==b.size());
    int n=a[0].size();
    matrix res(a.size(),row(b[0].size()));
    for (int i=0; i<a.size(); i++)
    {
        for (int j=0; j<b[0].size(); j++)
        {
            for (int k=0; k<n; k++)
                res[i][j]+=a[i][k]*b[k][j];
        }
    }
    return res;
}

row mul(matrix& a,row b)
{
    assert(a[0].size()==b.size());
    int n=a[0].size();
    row res(a.size(),0);
    for (int i=0; i<a.size(); i++)
    {
        for (int j=0; j<1; j++)
        {
            for (int k=0; k<n; k++)
                res[i]+=a[i][k]*b[k];
        }
    }
    return res;
}

matrix square(matrix m)
{
    return mul(m,m);
}

matrix sub(matrix a,matrix b)
{
    int n=a.size();
    for (int i=0; i<n; i++)
    {
        for (int j=0; j<n; j++)
        {
            a[i][j]-=b[i][j];
        }
    }
    return a;
}

matrix add(matrix a,matrix b)
{
    int n=a.size();
    for (int i=0; i<n; i++)
    {
        for (int j=0; j<n; j++)
        {
            b[i][j]+=a[i][j];
        }
    }
    return b;
}

row add(row& a,row b)
{
    for (int i=0; i<b.size(); i++)
        b[i]+=a[i];
    return b;
}

double sum(row& r)
{
    return accumulate(r.begin(), r.end(), 0.0);
}

vector<pair<pair<int,int>,pair<double,int> > > precalc(int a,int b,int n,double p0,double p1,double por,
        map<pair<int,int>,int> &m)
{
    vector<pair<pair<int,int>,pair<double,int> > > v;
    int p=1;
    for (int i=0; i<n; i++)
        p*=3;
    for (int i=0; i<p; i++)
    {
        int mask=i;
        double pr=1;
        for (int j=1; j<=n; j++)
        {
            if (mask%3==0) //0
            {
                pr*=p0;
            }
            if (mask%3==1) //1
            {
                pr*=p1;
            }
            if (mask%3==2) //|1
            {
                pr*=por;
            }
            mask/=3;
        }
        mask=i;
        int x=a,y=b;
        for (int j=1; j<=n; j++)
        {
            if (mask%3==0) //0
            {
                y*=2;
                if (y>=(1<<n))
                {
                    y-=(1<<n);
                    x=0;
                }
            }
            if (mask%3==1) //1
            {
                y=y+y+1;
                if (y>=(1<<n))
                {
                    y-=(1<<n);
                    x=0;
                }
            }
            if (mask%3==2) //|1
            {
                x|=y;
                y=1;
            }
            if (m.count({x,y}))
            {
                v.push_back({{x,y},{pr,j}});
                break;
            }
            mask/=3;
        }
    }
    return v;
}

double solve_prec(int n,double p0,double p1,double por)
{
    map<pair<int,int>,int> m;
    for (int i=0; i+1<(1<<n); i++)
    {
        int u=m.size();
        m[ {0,i}]=u;
    }
    for (int i=1; i+2<(1<<n); i++)
    {
        int u=m.size();
        m[ {i,1}]=u;
    }
    int u=m.size();
    for (int i=0; i<(1<<n); i++)
        for (int j=0; j<(1<<n); j++)
            if ((i|j)==(1<<n)-1)
                m[ {i,j}]=u;

    matrix mn=Z(u+1);
    matrix md=sub(Z(u+1),E(u+1));

    for (auto &p:m)
    {
        int a=p.first.first;
        int b=p.first.second;
        if ((a|b)==(1<<n)-1)
            continue;
        auto v=precalc(a,b,n,p0,p1,por,m);
        for (auto &x:v)
        {
            md[p.second][m[x.first]] += x.second.first;
            mn[p.second][m[x.first]] += x.second.first*x.second.second;
        }
    }

    md=inv(md);

    row V(u+1,0);
    V.back()=1;


    return mul(md,mul(mn,mul(md,V)))[0];
}

double solve_trivial(int n,double p0,double p1,double por)
{
    if (n>=5)
        return -1;
    int sz=(1<<(2*n));
    auto mat=Z(sz);
    for (int x=0; x<(1<<n); x++)
    {
        for (int y=0; y<(1<<n); y++)
        {
            if ((x|y)==(1<<n)-1)
            {
                continue;
            }
            mat[x*(1<<n)+y][(x|y)*(1<<n)+1]+=por;
            if (y*2<(1<<n))
            {
                mat[x*(1<<n)+y][x*(1<<n)+2*y+0]+=p0;
                mat[x*(1<<n)+y][x*(1<<n)+2*y+1]+=p1;
            }
            else
            {
                mat[x*(1<<n)+y][-1*(1<<n)+2*y+0]+=p0;
                mat[x*(1<<n)+y][-1*(1<<n)+2*y+1]+=p1;
            }
        }
    }
    mat=mul(mat,square(inv(sub(mat,E(sz)))));

    double ans=0;
    for (int x=0; x<(1<<n); x++)
    {
        for (int y=0; y<(1<<n); y++)
        {
            if ((x|y)==(1<<n)-1)
            {
                ans+=mat[0][x*(1<<n)+y];
            }
        }
    }

    return ans;
}

double solve_sum(int n,double p0,double p1,double por)
{
    if (n>=6)
        return -1;
    int sz=(1<<(2*n));
    auto mat=Z(sz);
    row R(sz,0);
    for (int x=0; x<(1<<n); x++)
    {
        for (int y=0; y<(1<<n); y++)
        {
            if ((x|y)==(1<<n)-1)
            {
                R[x*(1<<n)+y]=1;
                continue;
            }
            mat[x*(1<<n)+y][(x|y)*(1<<n)+1]+=por;
            if (y*2<(1<<n))
            {
                mat[x*(1<<n)+y][x*(1<<n)+2*y+0]+=p0;
                mat[x*(1<<n)+y][x*(1<<n)+2*y+1]+=p1;
            }
            else
            {
                mat[x*(1<<n)+y][-1*(1<<n)+2*y+0]+=p0;
                mat[x*(1<<n)+y][-1*(1<<n)+2*y+1]+=p1;
            }
        }
    }

    int C=(1<<25)/(sz*sz);
    if (n==1)
        C=1e3;

    double ans=0;
    for (int i=1; i<=C; i++)
    {
        R=mul(mat,R);
        ans+=i*R[0];
    }

    return ans;
}

double solve_sum_prec(int n,double p0,double p1,double por)
{
    map<pair<int,int>,int> m;
    for (int i=0; i+1<(1<<n); i++)
    {
        int u=m.size();
        m[ {0,i}]=u;
    }
    for (int i=1; i+2<(1<<n); i++)
    {
        int u=m.size();
        m[ {i,1}]=u;
    }
    int u=m.size();
    for (int i=0; i<(1<<n); i++)
        for (int j=0; j<(1<<n); j++)
            if ((i|j)==(1<<n)-1)
                m[ {i,j}]=u;

    vector<matrix> P(n+1,Z(u+1));

    for (auto &p:m)
    {
        int a=p.first.first;
        int b=p.first.second;
        if ((a|b)==(1<<n)-1)
            continue;
        auto v=precalc(a,b,n,p0,p1,por,m);
        for (auto &x:v)
        {
            P[x.second.second][p.second][m[x.first]] += x.second.first;
        }
    }

    double ans=0;

    int C=(1<<25)/(n*(u+1)*(u+1));
    if (n==1)
        C=1e3;

    vector<row> R(n+1,row(u+1,0));
    R[0].back()=1;

    for (int i=1; i<=C; i++)
    {
        int p=i%(n+1);
        R[p].assign(u+1,0);
        for (int j=1; j<=min(i,n); j++)
        {
            R[p]=add(R[p],mul(P[j],R[(p+n+1-j)%(n+1)]));
        }
        ans+=i*R[p][0];
    }

    return ans;
}

pair<double,int> solve_casino(int n,double p0,double p1,double por)
{
    const int C=1e5;
    long long int ans=0;
    mt19937 gen;
    uniform_real_distribution<double> dis(0,1);
    for (int i=1;i<=C;i++)
    {
        int x=0,y=0;
        while((x|y)!=(1<<n)-1)
        {
            ++ans;
            if (ans==2e8&&i==1){
                return {-1,-1};
            }
            auto r=dis(gen);
            if (r<p0) //0
            {
                y*=2;
                if (y>=(1<<n))
                {
                    y-=(1<<n);
                    x=0;
                }
            }
            else if (r<p0+p1) //1
            {
                y=y+y+1;
                if (y>=(1<<n))
                {
                    y-=(1<<n);
                    x=0;
                }
            }
            else
            {
                x|=y;
                y=1;
            }
        }
        if (ans>1e8)
        return {ans*1.0/i,i};
    }
    return {ans*1.0/C,C};
}

void go(int n,int a,int b,int c)
{
    assert(a+b+c==100);
    printf("%d %d %d %d\n",n,a,b,c);
    auto x1=solve_sum(n,a/100.0,b/100.0,c/100.0);
    auto x2=solve_trivial(n,a/100.0,b/100.0,c/100.0);
    auto x3=solve_sum_prec(n,a/100.0,b/100.0,c/100.0);
    auto x4=solve_prec(n,a/100.0,b/100.0,c/100.0);
    auto x5=solve_casino(n,a/100.0,b/100.0,c/100.0);
    printf("the approximate solution with 4^n x 4^n matrix         %.9f\n",x1);
    printf("the fine solution with 4^n x 4^n matrix                %.9f\n",x2);
    printf("the approximate solution with 2^(n+1) x 2^(n+1) matrix %.9f\n",x3);
    printf("the fine solution with 2^(n+1) x 2^(n+1) matrix        %.9f\n",x4);
    printf("the monte-carlo solution                               %.9f %d\n\n",x5.first,x5.second);
}

int main()
{
    vector<vector<int> > v;
    for (int i=1;i<=98;i++)
        for (int j=1;j<=98;j++)
            if (i+j<=99)
                v.push_back({i,j,100-i-j});
    /*int n;
    int a,b,c;
    scanf("%d\n0.%d 0.%d 0.%d",&n,&a,&b,&c);*/
    for (int n=1;n<=8;n++)
    {
        go(n,1,1,98);
        go(n,1,98,1);
        go(n,98,1,1);
        go(n,15,15,70);
        go(n,15,70,15);
        go(n,70,15,15);
        go(n,33,34,33);
        for (int i=0;i<3;i++)
        {
            int x=rand()%v.size();
            go(n,v[x][0],v[x][1],v[x][2]);
        }
    }

    return 0;
}


