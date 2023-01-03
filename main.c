#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "tinyexpr.h"

// if you want to compile and run the program,
// in command prompt enter:
//    1) gcc -g main.c tinyexpr.c -lm
//    2) ./a.exe

void freeSpace();
void nextStep(int n);
void printAnswer(int steps, int n);

#define COEF 20
#define MAX_LEN_VAR 10
#define MAX_LEN_EXPR 250
#define MAX_ITERATIONS 5000
#define EPS 1e-7
#define H 0.001

te_variable *vars;
char **var_names, **mat_expr;
double *x, *x_next, *fx, **mat_Jacobi;

void initFields(int n)
{
    x = malloc(n*sizeof(double));
    x_next = malloc(n*sizeof(double));
    fx = malloc(n*sizeof(double));
    var_names = malloc(n*sizeof(char*));
    mat_expr = malloc(n*sizeof(char*));
    mat_Jacobi = malloc(n*sizeof(double*));
    vars = malloc(n*sizeof(te_variable));

    if(x && x_next && fx && var_names && mat_expr && mat_Jacobi && vars)
    {
        for(int i = 0; i < n; i++)
        {
            *(x + i) = rand()%COEF + 5;
            var_names[i] = malloc(MAX_LEN_VAR*sizeof(char));
            mat_expr[i] = malloc(MAX_LEN_EXPR*sizeof(char));
            mat_Jacobi[i] = malloc(n*sizeof(double));
            if(var_names[i] && mat_expr[i] && mat_Jacobi[i])
            {
                sprintf(var_names[i], "x%d", i + 1);
                vars[i].name = var_names[i];
                vars[i].address = x + i;
            }
            else
            {
                printf("\nError in initialization!\n");
                freeSpace();
                exit(0);
            }
        }
    }
    else
    {
        printf("\nError in initialization!\n");
        freeSpace();
        exit(0);
    }
}

void getCofactor(double **mat, double **temp, int p, int q, int size)
{
    int i = 0, j = 0;
    for(int row = 0; row < size; row++)
    {
        for(int col = 0; col < size; col++)
        {
            if(row != p && col != q)
            {
                temp[i][j] = mat[row][col];
                j++;
                if(j == size - 1)
                {
                    j = 0;
                    i++;
                }
            }
        }
    }
}

double determinant(double **mat, int n)
{
    int i, j, k, factor = 1;
    double det = 0, **new_mat;
    if(mat == NULL)
    {
        printf("\nError in det calculation!\n");
        freeSpace();
        exit(0);
    }
    if(n == 1)
        return mat[0][0];
    for(i = 0; i < n; i++)
    {
        if(NULL == (new_mat = malloc((n - 1)*sizeof(double*))))
            return -1;
        for(j = 0; j < n - 1; j++)
            if(NULL == (new_mat[j] = malloc((n - 1)*sizeof(double))))
                return -1;

        for(j = 1; j < n; j++)
        {
            for (k = 0; k < n; k++)
            {
                if(k == i) continue;
                new_mat[j - 1][k < i ? k : (k - 1)] = mat[j][k];
            }
        }
        det += factor * mat[0][i] * determinant(new_mat, n - 1);
        factor *= -1;
        free(new_mat);
    }
    return det;
}

void adjointMat(double **mat, double **adj, int size)
{
    if(size == 1)
    {
        adj[0][0] = 1;
        return;
    }
    int sign = 1;
    double **temp = malloc(size*sizeof(double*));
    for(int i = 0; i < size; i++)
        temp[i] = malloc(size*sizeof(double));;

    for(int i = 0; i < size; i++)
    {
        for (int j = 0; j < size; j++)
        {
            getCofactor(mat, temp, i, j, size);
            sign = ((i + j)%2 == 0) ? 1 : -1;
            adj[j][i] = sign*determinant(temp, size - 1);
        }
    }
    free(temp);
}

double** inverseMat(double **mat, int size)
{
    double det = determinant(mat, size);
    if(det == 0)
    {
        printf("\nError! The system contains linearly dependent equations (det = 0): " \
                                    "check the correctness of the input!");
        freeSpace();
        exit(0);
    }
    double **adj = malloc(size*sizeof(double*)),
           **inv = malloc(size*sizeof(double*));

    for(int i = 0; i < size; i++)
    {
        adj[i] = malloc(size*sizeof(double));
        inv[i] = malloc(size*sizeof(double));
    }
    adjointMat(mat, adj, size);

    for(int i = 0; i < size; i++)
        for(int j = 0; j < size; j++)
            inv[i][j] = adj[i][j] / det;

    free(adj);
    return inv;
}

double getPartialDerivative(int pos_expr, int pos_x, int size)
{
    int err;
    te_expr *expr;

    *(x + pos_x) += H;
    expr = te_compile(*(mat_expr + pos_expr), vars, size, &err);
    if(err)
    {
        printf("\nError in getPartialDerivative h1!\n");
        freeSpace();
        exit(0);
    }
    const double h1 = te_eval(expr);

    *(x + pos_x) -= 2*H;
    expr = te_compile(*(mat_expr + pos_expr), vars, size, &err);
    if(err)
    {
        printf("\nError in getPartialDerivative h2!\n");
        freeSpace();
        exit(0);
    }
    const double h2 = te_eval(expr);

    *(x + pos_x) += H;
    te_free(expr);
    return (h1 - h2)/(2*H);
}

void fillMatJacobi(double **mat_Jacobi, int size)
{
    for(int i = 0; i < size; i++)
        for(int j = 0; j < size; j++)
            mat_Jacobi[i][j] = getPartialDerivative(i, j, size);
}

int iterCriterion(int size)
{
    for(int i = 0; i < size; i++)
        if(fabs(*(fx + i)) > EPS)
            return 1;
    return 0;
}

double* diffVec(double* a, double* b, int size)
{
    for(int i = 0; i < size; i++)
        *(a + i) -= *(b + i);
    return a;
}

void fillEquationVec(int size)
{
    int err;
    for(int i = 0; i < size; i++)
    {
        te_expr *expr = te_compile(*(mat_expr + i), vars, size, &err);
        if(err)
        {
            printf("\nError in fillEquationVec method!\n");
            freeSpace();
            exit(0);
        }
        const double tmp = te_eval(expr);
        *(fx + i) = tmp;
    }
}

double* getMatVecMultiplication(double **mat, double *vec, int size)
{
    double sm, *d_vec;
    d_vec = malloc(size*sizeof(double));

    for(int i = 0; i < size; i++)
    {
        sm = 0;
        for(int j = 0; j < size; j++)
            sm += mat[i][j]*vec[j];
        *(d_vec + i) = sm;
    }
    return d_vec;
}

void displayMat(double **mat, int size)
{
    for(int i = 0; i < size; i++)
    {
        for(int j=0;j<size;j++)
            printf("%lf ", mat[i][j]);
        printf("\n");
    }
    printf("\n");
}

void displayVec(double *vec, int size)
{
    for(int i = 0; i < size; i++)
        printf("%lf ", vec[i]);

    printf("\n");
}

void freeSpace()
{
    free(vars);
    free(mat_Jacobi);
    free(var_names);
    free(mat_expr);
    free(x_next);
    free(x);
}

int main()
{
    int n, err;
    printf("Greetings! Specify the num of variables: ");
    scanf("%d", &n);
    printf("Enter homogeneous system of equations --- >\n\n");
    initFields(n);

    for(int i = 0; i < n; i++)
    {
        printf("The %d equation: ", i + 1);
        scanf("%s", *(mat_expr + i));
        te_expr *t_expr = te_compile(*(mat_expr + i), vars, n, &err);
        if(err)
        {
            printf("\nError! Check the correctness of the input!\n");
            freeSpace();
            exit(0);
        }
    }
    nextStep(n);
    int steps = 0;

    while(iterCriterion(n) && steps < MAX_ITERATIONS)
    {
        x = x_next;
        nextStep(n);
        steps++;
    }
    printAnswer(steps, n);

    freeSpace();
    return 0;
}

void nextStep(int n)
{
    fillMatJacobi(mat_Jacobi, n);
    fillEquationVec(n);
    x_next = diffVec(x, getMatVecMultiplication(inverseMat(mat_Jacobi, n), fx, n), n);
}

void printAnswer(int steps, int n)
{
    printf("\nThe answer is:\n");
    for(int i = 0; i < n; i++)
        printf("x%d | %.5lf\n", i + 1, *(x_next + i));
    printf("---------\n");
    printf("Steps = %d\n", steps);

    displayVec(fx, n);
}