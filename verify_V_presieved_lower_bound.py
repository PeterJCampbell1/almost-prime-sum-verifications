import math

LIMIT = 10**10
SEGMENT_WIDTH = 10**8  # Increase to 10**9 for faster runs if sufficient RAM is available.

TAIL_EXPONENT = 6.2694
LEMMA_TARGET = 1.243

PRE_SIEVED_PRIMES = [3]
INITIAL_FACTOR = 0.5 # Accounts for p = 2 in the product

EXPECTED_PI_LIMIT = 455_052_511  # pi(10**10)


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


def odd_primes_in_segment(low, high, base_primes):
    """
    Yield odd primes p in the interval [low, high).

    The sieve stores only odd numbers.
    """
    if low % 2 == 0:
        low += 1

    # Odd numbers represented are low, low+2, low+4, ..., < high.
    segment_length = (high - low + 1) // 2
    is_prime = bytearray([1]) * segment_length

    for p in base_primes:
        if p == 2:
            continue

        if p * p >= high:
            break

        start = max(p * p, ((low + p - 1) // p) * p)

        if start % 2 == 0:
            start += p

        index = (start - low) // 2
        is_prime[index::p] = bytearray(len(is_prime[index::p]))

    # The index i represents the odd number low + 2*i.
    # Any entry still marked 1 is prime.
    for i, flag in enumerate(is_prime):
        if flag:
            yield low + 2 * i


def product_over_primes_segmented(limit, segment_width):
    """
    Compute

        1/2 * prod_{5 <= p < limit} (1 - 2/p)

    using a segmented sieve.
    """
    base_limit = int(math.isqrt(limit - 1)) + 1
    base_primes = primes_less_than(base_limit + 1)

    log_sum = 0.0
    prime_count = 0

    for low in range(5, limit, segment_width):
        high = min(low + segment_width, limit)

        for p in odd_primes_in_segment(low, high, base_primes):
            # The factor at p = 2 is accounted for by INITIAL_FACTOR.
            # Pre-sieved primes are omitted from the product.
            if p >= 3 and p not in PRE_SIEVED_PRIMES:
                # log1p(-2/p) is more accurate than log(1 - 2/p).
                log_sum += math.log1p(-2.0 / p)
                prime_count += 1

        print(f"finished segment [{low}, {high})")

    return INITIAL_FACTOR * math.exp(log_sum), prime_count


if __name__ == "__main__":
    product, prime_count = product_over_primes_segmented(
        LIMIT,
        SEGMENT_WIDTH,
    )

    lemma_constant = product * math.exp(TAIL_EXPONENT)

    total_prime_count = prime_count + 2  # Add primes 2 and 3.

    print()
    print("Finite product computation")
    print("--------------------------")
    print(f"limit            = {LIMIT:.2e}")
    print(f"segment width    = {SEGMENT_WIDTH:.2e}")
    print(f"number of primes = {total_prime_count}")
    print(f"expected pi      = {EXPECTED_PI_LIMIT}")
    print(f"prime count pass = {total_prime_count == EXPECTED_PI_LIMIT}")
    print(f"product          = {product:.18e}")
    print()
    print(f"tail exponent    = {TAIL_EXPONENT}")
    print(f"lemma constant   = {lemma_constant:.18e}")
    print(f"target           = {LEMMA_TARGET:.18e}")
    print(f"pass             = {lemma_constant > LEMMA_TARGET}")