import math

LIMIT = 10**8

# TAIL_EXPONENT is derived by hand (verifiable in one step, e.g. Wolfram Alpha):
#   log log 10^8 - 1/log^2 10^8       = 2.910526929...
#   1/(10^8-2) + 1/(10^8-1)           = 2.00000003e-8  < 1e-7
#   2(2.910526929...) - 1e-7          = 5.821053758... > 5.821
TAIL_EXPONENT = 5.821
LEMMA_TARGET = 1.241
FINITE_PRODUCT_LOWER_BOUND = 0.0036797

PRE_SIEVED_PRIMES = [3]
INITIAL_FACTOR = 0.5 # Accounts for p = 2 in the product

EXPECTED_PI_LIMIT = 5_761_455  # pi(10**8)


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


def product_over_primes(limit):
    """
    Compute
        1/2 * prod_{5 <= p < limit} (1 - 2/p).
    """
    primes = primes_less_than(limit)

    log_sum = 0.0
    prime_count = 0

    for p in primes:
        # The factor at p = 2 is accounted for by INITIAL_FACTOR.
        # Pre-sieved primes are omitted from the product.
        if p >= 3 and p not in PRE_SIEVED_PRIMES:
            # log1p(-2/p) is more accurate than log(1 - 2/p).
            log_sum += math.log1p(-2.0 / p)
            prime_count += 1

    return INITIAL_FACTOR * math.exp(log_sum), prime_count


if __name__ == "__main__":
    product, prime_count = product_over_primes(LIMIT)

    # Accounts for p = 2 and the pre-sieved prime p = 3.
    total_prime_count = prime_count + len(PRE_SIEVED_PRIMES) + 1

    prime_count_pass = total_prime_count == EXPECTED_PI_LIMIT
    finite_product_pass = product > FINITE_PRODUCT_LOWER_BOUND

    proof_constant = (
        FINITE_PRODUCT_LOWER_BOUND * math.exp(TAIL_EXPONENT)
    )
    proof_constant_pass = proof_constant > LEMMA_TARGET

    overall_pass = (
        prime_count_pass
        and finite_product_pass
        and proof_constant_pass
    )

    # This uses the computed product rather than its rounded lower bound.
    # It is included as an additional numerical diagnostic.
    unrounded_lemma_constant = product * math.exp(TAIL_EXPONENT)

    print()
    print("Finite product computation")
    print("--------------------------")
    print(f"limit                 = {LIMIT:.2e}")
    print(f"number of primes      = {total_prime_count}")
    print(f"expected pi           = {EXPECTED_PI_LIMIT}")
    print(f"prime count pass      = {prime_count_pass}")
    print(f"product               = {product:.18e}")
    print(f"finite lower bound    = {FINITE_PRODUCT_LOWER_BOUND:.18e}")
    print(f"finite product pass   = {finite_product_pass}")
    print()
    print("Lemma verification")
    print("------------------")
    print(f"tail exponent         = {TAIL_EXPONENT}")
    print(f"proof constant        = {proof_constant:.18e}")
    print(f"target                = {LEMMA_TARGET:.18e}")
    print(f"proof constant pass   = {proof_constant_pass}")
    print(f"unrounded constant    = {unrounded_lemma_constant:.18e}")
    print(f"overall pass          = {overall_pass}")