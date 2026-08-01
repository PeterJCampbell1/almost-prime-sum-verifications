import math

# Constants
CASE_1_BOUND = 1.0651
CASE_2_BOUND = 1.1282
CASE_3_BOUND = 1.1458
CASE_4_BOUND = 1.0356
CASE_5_BOUND = 1.0969
LEMMA_K_BOUND_P1 = 1.146 # Constant K for the Lemma
LEMMA_K_BOUND_P2 = 1.097
Z0_BASE = 117465180365547648498934439
Z0_EXPONENT = 16.5
Z0 = Z0_BASE ** (1.0 / Z0_EXPONENT)
W_ENDPOINT = 286
FIRST_PRIME_AT_OR_ABOVE_W_ENDPOINT = 293 # Smallest prime >= W_ENDPOINT
LAST_PRIME_BELOW_W_ENDPOINT = 283 # Greatest prime < W_ENDPOINT
Z1 = 10**8
# The list of pre-sieved primes can be modified for related computations.
PRE_SIEVED_PRIMES = [3]

ZETA_TAIL_CUTOFF = 100000 # Cutoff for zeta(2) calculations in Case 1 and 4


#####################
# HELPER FUNCTIONS
#####################
def primes_less_than(limit):
    """Return a list of all primes p < limit using a basic sieve."""
    if limit <= 2:
        return []

    is_prime = bytearray([1]) * limit
    is_prime[0] = is_prime[1] = 0

    for d in range(2, int(limit ** 0.5) + 1):
        if is_prime[d]:
            is_prime[d * d : limit : d] = bytearray(len(is_prime[d * d : limit : d]))

    return [n for n in range(2, limit) if is_prime[n]]


def zeta_two_tail_from(n0):
    """
    Return sum_{n >= n0} 1/n^2 using

        sum_{n >= n0} 1/n^2
        = pi^2/6 - sum_{n=1}^{n0-1} 1/n^2.
    """
    partial_sum = sum(1.0 / (n * n) for n in range(1, n0))
    return math.pi ** 2 / 6.0 - partial_sum



def upper_bound_factor(p):
    """
    Return the upper bound for (1 - g(p))^{-1} used in the proof.

    We use:
        p = 2  : 2
        odd p  : p/(p-2)

    Pre-sieved primes should be removed before this function is called.
    """
    if p == 2:
        return 2.0

    return p / (p - 2.0)

def product_upper_bound_from_w(w, primes, pre_sieved_primes):
    """
    Compute the product of the upper-bound factors over primes p >= w,
    excluding pre-sieved primes.
    """

    product = 1.0

    for p in primes:
        if p >= w and p not in pre_sieved_primes:
            product *= upper_bound_factor(p)

    return product

def case_3_z_candidates(z0, w_endpoint):
    """
    Return the z-candidates used in Case 3.

    The candidates are:
        z = z0,
        and right-hand limiting values z -> q^+,
    where q runs over primes with z0 <= q < w_endpoint.

    Each candidate is returned as:
        (label, log_z, included_primes),
    where included_primes is the list of primes included in the product.
    """
    primes = primes_less_than(w_endpoint)

    candidates = []

    # Candidate z = z0.
    # This records the primes satisfying p < z0.
    # The later product computation will impose p >= w and remove pre-sieved primes.
    included_primes = [
        p for p in primes
        if p < z0
    ]
    candidates.append(("z0", math.log(z0), included_primes))

    # Candidates z -> q^+.  The included primes are p <= q.
    for q in primes:
        if z0 <= q < w_endpoint:
            included_primes = [
                p for p in primes
                if p <= q
            ]
            candidates.append((f"{q}+", math.log(q), included_primes))

    return candidates


#####################
# CASE 1
#####################
def check_case_1_large_w(lower_prime, cutoff):
    """
    Compute the Case 1 constant.

    This computes

        exp( 2/log(lower_prime)^2
             + 2 * ( sum_{lower_prime <= p < cutoff} 1/(p(p-2))
                     + sum_{n >= cutoff-2} 1/n^2 ) ).
    """

    primes = primes_less_than(cutoff)

    prime_sum = sum(
        1.0 / (p * (p - 2))
        for p in primes
        if lower_prime <= p
    )

    tail = zeta_two_tail_from(cutoff - 2)

    exponent_bound = (
        2.0 / (math.log(lower_prime) ** 2)
        + 2.0 * (prime_sum + tail)
    )

    return math.exp(exponent_bound)

#####################
# CASE 2 AND CASE 5
#####################
def check_small_w_large_z(
    large_prime_bound,
    lower_prime_large_tail,
    upper_prime_finite_product,
    w_endpoint,
    pre_sieved_primes,
):
    """
    Compute the finite small-w maximum for Cases 2 and 5 of the proof:

        sup  large_prime_bound
             * (log(w)/log(lower_prime_large_tail))^2
             * product_upper_bound_from_w(w).

    By the monotonicity argument in the proof, it is enough to check
    the non-pre-sieved prime endpoints together with the limiting
    endpoint w -> w_endpoint^-.
    """
    primes = primes_less_than(upper_prime_finite_product + 1)

    w_candidates = [
        p for p in primes
        if p not in pre_sieved_primes
    ]
    w_candidates.append(w_endpoint)

    best_value = 0.0
    best_w = None

    for w in w_candidates:
        product = product_upper_bound_from_w(
            w,
            primes,
            pre_sieved_primes,
        )

        value = (
            large_prime_bound
            * (math.log(w) / math.log(lower_prime_large_tail)) ** 2
            * product
        )

        if value > best_value:
            best_value = value
            best_w = w

    return best_value, best_w

#####################
# CASE 3
#####################
def check_case_3_finite_z_range(z0, w_endpoint, pre_sieved_primes):
    """
    Compute the Case 3 finite maximum.

    This computes the supremum over z0 <= z < w_endpoint and 2 <= w < z
    after reducing to the finite list of z-candidates described in the proof.
    """
    best_value = 0.0
    best_w = None
    best_z_label = None

    z_candidates = case_3_z_candidates(z0, w_endpoint)

    for z_label, log_z, included_primes in z_candidates:

        # Candidate w-values from the proof: non-pre-sieved prime endpoints.
        w_candidates = [
            p for p in included_primes
            if p not in pre_sieved_primes
        ]

        for w in w_candidates:
            product = product_upper_bound_from_w(
                w,
                included_primes,
                pre_sieved_primes,
            )

            value = product * (math.log(w) / log_z) ** 2

            if value > best_value:
                best_value = value
                best_w = w
                best_z_label = z_label

    return best_value, best_w, best_z_label

#####################
# CASE 4
#####################
def check_case_4_z_geq_z1(z1, lower_prime, cutoff):
    """
    Compute the Case 4 constant.

    This computes

        exp( 1/log(z1)^2 + 1/log(lower_prime)^2
             + 2 * ( sum_{lower_prime <= p < cutoff} 1/(p(p-2))
                     + sum_{n >= cutoff-2} 1/n^2 ) ).
    """

    primes = primes_less_than(cutoff)

    prime_sum = sum(
        1.0 / (p * (p - 2))
        for p in primes
        if lower_prime <= p
    )

    tail = zeta_two_tail_from(cutoff - 2)

    exponent_bound = (
        1.0 / (math.log(z1) ** 2)
        + 1.0 / (math.log(lower_prime) ** 2)
        + 2.0 * (prime_sum + tail)
    )

    return math.exp(exponent_bound)


if __name__ == "__main__":
    case_1_constant = check_case_1_large_w(
        FIRST_PRIME_AT_OR_ABOVE_W_ENDPOINT,
        ZETA_TAIL_CUTOFF,
    )

    case_2_constant, case_2_w = check_small_w_large_z(
        CASE_1_BOUND,
        FIRST_PRIME_AT_OR_ABOVE_W_ENDPOINT,
        LAST_PRIME_BELOW_W_ENDPOINT,
        W_ENDPOINT,
        PRE_SIEVED_PRIMES,
    )

    case_3_constant, case_3_w, case_3_z = check_case_3_finite_z_range(
        Z0,
        W_ENDPOINT,
        PRE_SIEVED_PRIMES,
    )

    case_4_constant = check_case_4_z_geq_z1(
        Z1,
        FIRST_PRIME_AT_OR_ABOVE_W_ENDPOINT,
        ZETA_TAIL_CUTOFF,
    )

    case_5_constant, case_5_w = check_small_w_large_z(
        CASE_4_BOUND,
        FIRST_PRIME_AT_OR_ABOVE_W_ENDPOINT,
        LAST_PRIME_BELOW_W_ENDPOINT,
        W_ENDPOINT,
        PRE_SIEVED_PRIMES,
    )

    overall_pass_p1 = (
        case_1_constant < CASE_1_BOUND
        and case_2_constant < CASE_2_BOUND
        and case_3_constant < CASE_3_BOUND
        and CASE_1_BOUND < LEMMA_K_BOUND_P1
        and CASE_2_BOUND < LEMMA_K_BOUND_P1
        and CASE_3_BOUND < LEMMA_K_BOUND_P1
    )

    overall_pass_p2 = (
        case_4_constant < CASE_4_BOUND
        and case_5_constant < CASE_5_BOUND
        and CASE_4_BOUND < LEMMA_K_BOUND_P2
        and CASE_5_BOUND < LEMMA_K_BOUND_P2
    )

    print("Case 1: large-w constant")
    print("------------------------")
    print(f"lower prime       = {FIRST_PRIME_AT_OR_ABOVE_W_ENDPOINT}")
    print(f"cutoff            = {ZETA_TAIL_CUTOFF}")
    print()
    print(f"computed constant = {case_1_constant:.14f}")
    print(f"target bound      = {CASE_1_BOUND:.14f}")
    print(f"case 1 pass       = {case_1_constant < CASE_1_BOUND}")
    print()
    print()
    print("Case 2: small-w, large-z constant")
    print("---------------------------------")
    print(f"w endpoint                 = {W_ENDPOINT}")
    print(f"large-tail prime           = {FIRST_PRIME_AT_OR_ABOVE_W_ENDPOINT}")
    print(f"finite product up to prime = {LAST_PRIME_BELOW_W_ENDPOINT}")
    print(f"pre-sieved primes          = {PRE_SIEVED_PRIMES}")
    print()
    print(f"computed constant          = {case_2_constant:.14f}")
    print(f"target bound               = {CASE_2_BOUND:.14f}")
    print(f"attained at w              = {case_2_w}")
    print(f"case 2 pass                = {case_2_constant < CASE_2_BOUND}")
    print()
    print()
    print("Case 3: finite z-range constant")
    print("-------------------------------")
    print(f"z0                 = {Z0:.14f}")
    print(f"z range upper end  = {W_ENDPOINT}")
    print(f"pre-sieved primes  = {PRE_SIEVED_PRIMES}")
    print()
    print(f"computed constant  = {case_3_constant:.14f}")
    print(f"target bound       = {CASE_3_BOUND:.14f}")
    print(f"attained at w      = {case_3_w}")
    print(f"attained at z      = {case_3_z}")
    print(f"case 3 pass        = {case_3_constant < CASE_3_BOUND}")
    print()
    print()
    print("Case 4: large-w constant for z >= z1")
    print("-------------------------------------")
    print(f"z1                = {Z1}")
    print(f"lower prime       = {FIRST_PRIME_AT_OR_ABOVE_W_ENDPOINT}")
    print(f"cutoff            = {ZETA_TAIL_CUTOFF}")
    print()
    print(f"computed constant = {case_4_constant:.14f}")
    print(f"target bound      = {CASE_4_BOUND:.14f}")
    print(f"case 4 pass       = {case_4_constant < CASE_4_BOUND}")
    print()
    print()
    print("Case 5: small-w constant for z >= z1")
    print("------------------------------------")
    print(f"w endpoint                 = {W_ENDPOINT}")
    print(f"large-tail prime           = {FIRST_PRIME_AT_OR_ABOVE_W_ENDPOINT}")
    print(f"finite product up to prime = {LAST_PRIME_BELOW_W_ENDPOINT}")
    print(f"pre-sieved primes          = {PRE_SIEVED_PRIMES}")
    print()
    print(f"computed constant          = {case_5_constant:.14f}")
    print(f"target bound               = {CASE_5_BOUND:.14f}")
    print(f"attained at w              = {case_5_w}")
    print(f"case 5 pass                = {case_5_constant < CASE_5_BOUND}")
    print()
    print()
    print("Overall verification")
    print("--------------------")
    print(f"lemma K bound assertion (1) = {LEMMA_K_BOUND_P1:.14f}")
    print(f"case 1 bound < lemma bound  = {CASE_1_BOUND < LEMMA_K_BOUND_P1}")
    print(f"case 2 bound < lemma bound  = {CASE_2_BOUND < LEMMA_K_BOUND_P1}")
    print(f"case 3 bound < lemma bound  = {CASE_3_BOUND < LEMMA_K_BOUND_P1}")
    print(f"pass of assertion (1)       = {overall_pass_p1}")
    print(f"lemma K bound assertion (2) = {LEMMA_K_BOUND_P2:.14f}")
    print(f"case 4 bound < lemma bound  = {CASE_4_BOUND < LEMMA_K_BOUND_P2}")
    print(f"case 5 bound < lemma bound  = {CASE_5_BOUND < LEMMA_K_BOUND_P2}")
    print(f"pass of assertion (2)       = {overall_pass_p2}")
