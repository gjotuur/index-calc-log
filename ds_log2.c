#include <stdio.h>
#include <math.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define MAX_FACTOR_BASE 1000
#define MAX_EQUATIONS 1500
#define C_CONSTANT 20

//Algebraic group
typedef struct {
    uint64_t module;
    uint64_t generator;
    uint64_t order;
} AlgebraicGroup;

//Factorbase
typedef struct {
    uint64_t primes[MAX_FACTOR_BASE];
    int size;
} FactorBase;

//Solve
typedef struct {
    int64_t **A;
    int64_t *b;
    int rows;
    int cols;
} EquationSystem;

// Функція для швидкого піднесення до степеня за модулем
uint64_t ring_mul(uint64_t base, uint64_t exp, uint64_t mod) {
    uint64_t result = 1;
    base %= mod;
    while (exp > 0) {
        if (exp & 1) {
            result = (__uint128_t)result * base % mod;
        }
        base = (__uint128_t)base * base % mod;
        exp >>= 1;
    }
    return result;
}

//Different approach - Rabin test
bool MR_test(uint64_t n, uint64_t a) {
    if (n < 2) return false;
    if (n == 2) return true;
    if (n % 2 == 0) return false;
    
    uint64_t d = n - 1;
    int k = 0;
    while (d % 2 == 0) {
        d /= 2;
        k++;
    }
    
    uint64_t x = ring_mul(a, d, n);
    if (x == 1 || x == n - 1) return true;
    
    for (int i = 0; i < k - 1; i++) {
        x = (__uint128_t)x * x % n;
        if (x == n - 1) return true;
    }
    return false;
}

//Primeness
bool is_prime(uint64_t n) {
    if (n < 2) return false;
    if (n == 2 || n == 3) return true;
    if (n % 2 == 0) return false;
    
    // Тестуємо з декількома базами
    uint64_t bases[] = {2, 3, 5, 7, 11, 13, 17, 19, 23};
    for (int i = 0; i < 9; i++) {
        if (n == bases[i]) return true;
        if (!MR_test(n, bases[i])) return false;
    }
    return true;
}

//GCD, simplistic
uint64_t gcd(uint64_t a, uint64_t b) {
    while (b) {
        uint64_t t = b;
        b = a % b;
        a = t;
    }
    return a;
}

//EEA, actually
int64_t ring_inv(int64_t a, int64_t m) {
    int64_t m0 = m, x0 = 0, x1 = 1;
    if (m == 1) return 0;
    
    a = ((a % m) + m) % m;
    while (a > 1) {
        int64_t q = a / m;
        int64_t t = m;
        m = a % m;
        a = t;
        t = x0;
        x0 = x1 - q * x0;
        x1 = t;
    }
    if (x1 < 0) x1 += m0;
    return x1;
}

//Factorbase generation
void generate_fb(uint64_t n, FactorBase *base) {
    double log_n = log((double)n);
    double log_log_n = log(log_n);
    int B_lim = (int)(3.38 * exp(0.5 * sqrt(log_n * log_log_n)));
    
    printf("Factor Base limit: %d\n", B_lim);
    
    base->size = 0;
    for (int a = 2; a < B_lim && base->size < MAX_FACTOR_BASE; a++) {
        if (is_prime(a)) {
            base->primes[base->size++] = a;
        }
    }
    printf("Factor base size: %d\n", base->size);
}

//B-smoothness. again
bool b_smooth(uint64_t val, FactorBase *base, int *powers) {
    memset(powers, 0, base->size * sizeof(int));
    
    for (int i = 0; i < base->size; i++) {
        while (val % base->primes[i] == 0) {
            powers[i]++;
            val /= base->primes[i];
        }
    }
    
    return val == 1;
}

//Generation of equation system
bool generate_eq(uint64_t a, uint64_t n, FactorBase *base, EquationSystem *sys) {
    clock_t start = clock();
    
    int number_of_eq = base->size + C_CONSTANT;
    sys->cols = base->size;
    sys->rows = 0;
    
    // Виділяємо пам'ять
    sys->A = (int64_t**)malloc(number_of_eq * sizeof(int64_t*));
    sys->b = (int64_t*)malloc(number_of_eq * sizeof(int64_t));
    
    for (int i = 0; i < number_of_eq; i++) {
        sys->A[i] = (int64_t*)malloc(base->size * sizeof(int64_t));
    }
    
    uint64_t curr_power = 1;
    uint64_t curr_val = a;
    int *powers = (int*)malloc(base->size * sizeof(int));
    
    while (sys->rows < number_of_eq) {
        if (b_smooth(curr_val, base, powers)) {
            for (int j = 0; j < base->size; j++) {
                sys->A[sys->rows][j] = powers[j];
            }
            sys->b[sys->rows] = curr_power;
            sys->rows++;
        }
        
        curr_val = (__uint128_t)curr_val * a % n;
        curr_power++;
        
        if (curr_val == 1) break;
        if (curr_power > n) break;  // Запобігання нескінченному циклу
    }
    
    free(powers);
    
    clock_t end = clock();
    printf("Generated equations: %d\n", sys->rows);
    printf("Generating time: %.3f seconds\n\n", (double)(end - start) / CLOCKS_PER_SEC);
    
    return sys->rows >= base->size;
}

//Solve system
void solve_eq(EquationSystem *sys, uint64_t mod, int64_t *solution) {
    int m = sys->cols;
    int n = sys->rows;
    
    // Створюємо розширену матрицю A|b
    int64_t **A = (int64_t**)malloc(n * sizeof(int64_t*));
    for (int i = 0; i < n; i++) {
        A[i] = (int64_t*)malloc((m + 1) * sizeof(int64_t));
        memcpy(A[i], sys->A[i], m * sizeof(int64_t));
        A[i][m] = sys->b[i];
    }
    
    bool *chosen = (bool*)calloc(n, sizeof(bool));
    
    // Метод Гауса
    for (int j = 0; j < m; j++) {
        bool found = false;
        
        // Шукаємо рядок з оборотним елементом
        for (int i = 0; i < n; i++) {
            if (chosen[i]) continue;
            
            int64_t a_ij = ((A[i][j] % (int64_t)mod) + (int64_t)mod) % (int64_t)mod;
            if (gcd(a_ij, mod) == 1) {
                chosen[i] = true;
                found = true;
                
                int64_t inv = ring_inv(a_ij, mod);
                for (int k = 0; k <= m; k++) {
                    A[i][k] = ((__int128_t)A[i][k] * inv) % (int64_t)mod;
                    if (A[i][k] < 0) A[i][k] += mod;
                }
                
                // Віднімаємо від інших рядків
                for (int k = 0; k < n; k++) {
                    if (k != i && A[k][j] != 0) {
                        int64_t factor = A[k][j];
                        for (int l = 0; l <= m; l++) {
                            A[k][l] = ((A[k][l] - (__int128_t)factor * A[i][l]) % (int64_t)mod + (int64_t)mod) % (int64_t)mod;
                        }
                    }
                }
                break;
            }
        }
        
        // Якщо не знайшли оборотний, шукаємо з НСД > 1
        if (!found) {
            for (int i = 0; i < n; i++) {
                if (chosen[i] || A[i][j] == 0) continue;
                
                int64_t d = gcd(abs(A[i][j]), mod);
                if (d > 1) {
                    // Перевіряємо чи всі елементи діляться на d
                    bool all_divisible = true;
                    for (int k = 0; k <= m; k++) {
                        if (A[i][k] % d != 0) {
                            all_divisible = false;
                            break;
                        }
                    }
                    
                    if (all_divisible) {
                        chosen[i] = true;
                        for (int k = 0; k <= m; k++) {
                            A[i][k] /= d;
                        }
                        
                        int64_t inv = ring_inv(A[i][j], mod);
                        for (int k = 0; k <= m; k++) {
                            A[i][k] = ((__int128_t)A[i][k] * inv) % (int64_t)mod;
                            if (A[i][k] < 0) A[i][k] += mod;
                        }
                        
                        for (int k = 0; k < n; k++) {
                            if (k != i && A[k][j] != 0) {
                                int64_t factor = A[k][j];
                                for (int l = 0; l <= m; l++) {
                                    A[k][l] = ((A[k][l] - (__int128_t)factor * A[i][l]) % (int64_t)mod + (int64_t)mod) % (int64_t)mod;
                                }
                            }
                        }
                        break;
                    }
                }
            }
        }
    }
    
    // Витягуємо розв'язок
    for (int j = 0; j < m; j++) {
        solution[j] = 0;
        for (int i = 0; i < n; i++) {
            if (A[i][j] != 0) {
                solution[j] = A[i][m];
                break;
            }
        }
    }
    
    // Очищення пам'яті
    for (int i = 0; i < n; i++) {
        free(A[i]);
    }
    free(A);
    free(chosen);
}

//Index Calculus here boi
int64_t IC_method(uint64_t a, uint64_t beta, uint64_t n, FactorBase *base, int64_t *S_idxs) {
    uint64_t curr_ind = 0;
    uint64_t curr_val = beta;
    int *powers = (int*)malloc(base->size * sizeof(int));
    
    for (uint64_t iter = 0; iter < n - 1; iter++) {
        if (b_smooth(curr_val, base, powers)) {
            int64_t corr_a_ind = 0;
            for (int i = 0; i < base->size; i++) {
                corr_a_ind = (corr_a_ind + (__int128_t)S_idxs[i] * powers[i]) % (n - 1);
            }
            
            int64_t result = (corr_a_ind - (int64_t)curr_ind) % (int64_t)(n - 1);
            if (result < 0) result += (n - 1);
            
            free(powers);
            return result;
        }
        
        curr_ind++;
        curr_val = (__uint128_t)curr_val * a % n;
    }
    
    free(powers);
    return -1;  // Не знайдено
}

//Main
int64_t dlog_IC(uint64_t alpha, uint64_t beta, uint64_t n) {
    FactorBase base;
    EquationSystem sys;
    
    printf("Generating factor base...\n");
    generate_fb(n, &base);
    
    printf("Generating equations...\n");
    if (!generate_eq(alpha, n, &base, &sys)) {
        printf("Not enough equations generated!\n");
        return -1;
    }
    
    printf("Solving modular equations...\n");
    int64_t *S_idxs = (int64_t*)malloc(base.size * sizeof(int64_t));
    solve_eq(&sys, n - 1, S_idxs);
    
    printf("Finding discrete logarithm...\n");
    int64_t result = IC_method(alpha, beta, n, &base, S_idxs);
    
    // Очищення пам'яті
    for (int i = 0; i < sys.rows; i++) {
        free(sys.A[i]);
    }
    free(sys.A);
    free(sys.b);
    free(S_idxs);
    
    return result;
}

//Init Algebraic group
void init_group(AlgebraicGroup* group, uint64_t module, uint64_t generator) {
    group->generator = generator;
    group->module = module;
    group->order = module - 1;
}

int main() {
    printf("There is no life \n");
    printf("==========================\n\n");
    
    uint64_t a, b, n;
    
    printf("Enter parameters:\n");
    printf("Generator (a): ");
    scanf("%llu", &a);
    printf("Value (b): ");
    scanf("%llu", &b);
    printf("Modulus (n - prime): ");
    scanf("%llu", &n);
    
    printf("\n");
    
    clock_t start = clock();
    int64_t result = dlog_IC(a, b, n);
    clock_t end = clock();
    
    printf("\n==========================\n");
    if (result >= 0) {
        printf("Solution: %lld\n", result);
        printf("Verification: %llu^%lld ≡ %llu (mod %llu)\n", a, result, ring_mul(a, result, n), n);
    } else {
        printf("Solution not found!\n");
    }
    printf("Total execution time: %.3f seconds\n", (double)(end - start) / CLOCKS_PER_SEC);
    
    return 0;
}