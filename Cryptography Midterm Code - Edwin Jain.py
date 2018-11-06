import math, random, itertools


def extended_euclidean(x, y):
    """ 
    Given two numbers x, y this function runs the Extended Euclidean
    Algorithm and returns the greatest common divisor along with the
    multiples required to write the gcd as a linear combination of the
    original two numbers.

    Arguments:
    - x: A positive integer
    - y: A positive integer

    Returns 3 ints:
    - x: The gcd
    - u_i, v_i such that x*u_i + y*v_i = GCD
    """

    u_i, u_j = 1, 0
    v_i, v_j = 0, 1
    while y != 0:
        quotient, remainder = divmod(x, y)

        # Update the linear combinations
        u_i, u_j = u_j, u_i - quotient * u_j 
        v_i, v_j = v_j, v_i - quotient * v_j
        
        # Update the x and y, and repeat if remainder isn't 0 yet
        x, y = y, remainder 
    return x, u_i, v_i 


def gcd(x, y):
    """
    Runs the extended Euclidean algorithm and returns the gcd of x and y,
    which are assumed to be positive integers
    """
    return extended_euclidean(x,y)[0]


def modular_inverse(a, m):
    """
    Runs the extended Euclidean algorithm and returns the inverse b of 
    a (mod p), i.e. ab = 1 (mod m). Both a and m are assumed to be positive
    integers. 

    Returns 0 if no inverse is possible.
    """
    x, u, v = extended_euclidean(a, m)
    return 0 if x == a else u


def fast_pow(g, A, N):
    """
    Uses the fast powering algorithm to compute g^A (mod N) efficiently. 

    Arguments:
    g - Base (positive integer)
    A - Exponent (positive integer)
    N - Modulus (positive integer)

    Returns: A positive integer
    """

    a = g
    b = 1
    # While we have more exponentiation to do
    while A > 0:

        # If exponent is odd
        if A & 1 == 1:
            b = (b*a) % N
        
        # If exponent is even, square our number and divide the exponent by 2.
        a = (a**2) % N
        A = A >> 1 # Right-shift by 1 = Divide by 2 
   
    return b 


def shanks_alg(g, h, p):
    """
    Given ints g, h, and p, this function solves the discrete log problem
    g^x = h (mod p) using Shank's Babystep-Giantstep Algorithm.

    Arguments:
    g: Base (positive integer)
    h: Result (positive integer)
    p: Modulus (usually prime)

    Returns: A positive integer exponent x that solves the DLP
    """
    ans = 0
    n = math.floor(math.sqrt(p-1)) + 1

    # Create the first list of g^i
    l1 = [pow(g, i, p) for i in range(n)]

    # Calculate g's inverse mod p
    g_inv = pow(g, n * (p-2), p)
    
    for j in range(n):

        # Get the next element of the second list: h*g_inv^j 
        h_next = (h * pow(g_inv, j, p)) % p

        # If we find a match, break out and return the answer
        ans = [j*n + i for i in range(len(l1)) if h_next == l1[i]]
        if ans: break

    return ans[0]
    

def prime_factors(n):
    """
    Returns the prime factors of n as a Counter. As a dict, this looks
    like {prime: exponent} for each of the primes in n's factorization.
    Assumes that n is a positive integer.
    """
    i = 2
    factors = []
    exps = []
    while i * i <= n:
        if n % i:
            i += 1
        else:
            n //= i
            factors.append(i)
    if n > 1:
        factors.append(n)
    return Counter(factors)


def chinese_remainder(pairs):
    """
    Given a set of congruences x = a (mod m), this uses the Chinese 
    Remainder Theorem to solve for x. 

    Arguments:
    - pairs: List of tuples (a, m), where a is the result and m is the modulus

    Returns: A positive integer x that solves all the congruences.
    """

    # Find the product of all the moduli
    N, ans = pairs[0][1], 0
    for (a, n) in pairs[1:]:
        N *= n

    # For each congruence, we use a modular inverse calculation and 
    # add to the final answer.
    for (a_i, n_i) in pairs:
        q_i = N // n_i
        inv = modular_inverse(q_i, n_i)
        ans += q_i * a_i * inv
    return ans % N


def pohlig_hellman(g, h, p):
    """
    Solves for x in the discrete log problem g^x = h (mod p) using
    the Pohlig-Hellman Algorithm. 

    Arguments:
    - g: Base (positive integer)
    - h: Result (positive integer)
    - p: Modulus (usually a prime)

    Returns: A positive integer exponent x that solves the DLP
    """
    N = p-1

    # Get prime factorization of the p-1
    pf = dict(prime_factors(p-1))
    factors, exps = list(pf.keys()), list(pf.values())

    congruences = []

    # For each factor-exp pair, find g_i and h_i and solve for y_i using
    # Shank's algorithm. Then, we have a new congruence that factor^exp
    # must be congruent to y_i (mod p-1). 
    for i in range(len(factors)):
        qe_i = factors[i] ** exps[i]
        g_i, h_i = pow(g, N//qe_i, p), pow(h, N//qe_i, p)
        y_i = shanks_alg(g_i, h_i, p)
        congruences.append((y_i, qe_i))

    # Solve the congruences with the Chinese Remainder Theorem
    return chinese_remainder(congruences)


def RSA_encrypt(N, e, m):
    """
    Performs RSA encryption as the sender and returns the ciphertext.
    This just requires computing m^e (mod N).

    Arguments:
    - N: Modulus (positive integer)
    - e: The chosen, publicly known e such that gcd(e, (p-1)*(q-1)) = 1
    - m: Message (positive integer)

    Returns: Ciphertext c (also a positive integer)
    """
    return pow(m, e, N)


def RSA_decrypt(c, p, q, e):
    """
    This decrypts an RSA ciphertext c given publicly known e and
    private primes p and q, and returns the original message m.

    Arguments:
    - c: Ciphertext (positive integer)
    - p: Private prime number (positive integer)
    - q: Private prime number (positive integer)
    - e: Publicly chosen number (positive integer)
    """
    d = modular_inverse(e, (p-1)*(q-1)) # Inverse of e
    return pow(c, d, p*q)


def pollards_factorization_alg(N, bound=50):
    """
    Runs Pollard's p-1 factorization algorithm to find a factor of N.
    Assumes N and bound are positive integers.

    Arguments:
    - N: The number to be factored
    - bound: The number of factors to check

    Returns: The factor found (a positive integer), and if none is found, 0.
    """
    a = 2

    # For numbers j under our bound, compute a^j (mod N) and
    # check whether they factor into N.
    for j in range(2, bound):
        a = pow(a, j, N)
        d = gcd(a-1, N)

        # If we find a factor, we're done
        if d > 1 and d < N:
            return d
    return 0


def pollards_rho_method(g, h, p, seed=2):
    """
    Incomplete implementation of Pollard's rho method. Will eventually
    find x to solve the DLP g^x = h (mod p).

    Arguments:
    - g: Base (positive integer)
    - h: Result (positive integer)
    - p: Modulus (positive integer)
    - seed: Random number (positive integer, default=2)
    """
    a_0, b_0, a_1, b_1 = seed, seed, seed, seed
    x_0 = (pow(g, a_1, p) * pow(h, b_1, p)) % p
    x_1 = x_0

    # Computes one forward step given a starting x, and exponents a and b
    def forward(x, a, b):
        if x > p//3:

            # Case 1: Multiply by h, increment b
            if x > 2*p//3:
                return (h*x) % p, a, b+1
            

            # Case 2: Square x, increment both a and b
            else:
                return pow(x, 2, p), 2*a, 2*b

        # Case 3: Multiply by g, increment a
        else:
            return (g*x) % p, a+1, b

    while True:
        # Compute one forward step, and two forward steps at a time
        x_0, a_0, b_0 = forward(x_0, a_0, b_0)
        x_1, a_1, b_1 = forward(*forward(x_1, a_1, b_1))

        # If we find a match, we stop computing forward orbits
        if (x_0 == x_1):
            break

    # Everything above this part of the code works, but the next section
    # currently returns wrong answers. 
    u, v = (a_0 - a_1) % (p-1), (b_1 - b_0) % (p-1)
    v_inv = modular_inverse(v, p-1)
    return (u*v_inv) % (p-1)





