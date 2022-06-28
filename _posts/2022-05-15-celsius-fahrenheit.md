---
layout: post
title: How to convert quickly between ℃ and ℉
hasmath: true
date: 2022-06-22 21:48 -0700
---
As a speaker of multiple languages, I'm often aware of how inherent
habits in our speech can greatly influence the extent to which other
people make sense of it.  But even when you speak the same language,
even a topic as simple as the weather can already bring unnecessary
friction to the conversation if the speakers are using incompatible
units (_cough_ _cough_).  Or maybe I'm just coming up with an
arbitrary reason to justify this party trick.  In any case, I describe
a mental heuristic that gets you within 0.25℃ for any temperature in
Fahrenheit, and prove the error bound.  For the other direction, the
error in converting a temperature in Celsius to Fahrenheit is at most
0.5℉.

With this method, you get an immediate sense of the rough temperature
in Celsius for a given temperature in Fahrenheit, and if you calculate
a bit more, then the error is 0.25℃.

## Anchor points
I memorize the following table.  I recommend remembering that 50℉
corresponds to 10℃. Since Fahrenheit and Celsius have a linear
relationship, a difference of 9℉ corresponds to a difference of 5℃.
You can get the other numbers by adding as needed.

| Fahrenheit | Celsius |
|------------|---------|
| 32         | 0       |
| 41         | 5       |
| **50**     | **10**  |
| 59         | 15      |
| 68         | 20      |
| 77         | 25      |
| 86         | 30      |

## Steps to perform the conversion

Given a temperature $$T_F$$ and the table,

1. Look up the nearest Farenheit value $$v$$ in the table.  If it
   exists then you are done and the answer is $$T[v]$$.
2. Otherwise, compute $$\frac{T_F-T[v]}{2}$$, let the result
   be $$d$$
3. The approximation is given by $$T[v]+d$$

Here's an example.

1. Suppose we are given 72℉.  The nearest value in the table is 68℉,
   corresponding to 20℃.
2. Now we compute $$\frac{72-68}{2}=2$$
3. Now we add the two results to get 22℃.

## Code
I can render the above steps into code so it's unambiguous what I
actually mean.  Note that in the code I didn't use a lookup table but
instead some arithmetic to find the closest anchor point.  Obviously
in practice it'll be memorized.

```python
def convert_approx(given):
    # Nearest memorized temperature
    close = round((given - 5) / 9) * 9 + 5
    # Convert to Celsius
    rough = (close - 32) // 9
    # Half of the difference
    diff = (given - close) / 2
    return rough + diff
```

## Proof of error bound
First observe since the memorized intervals occur every 9℉, the
difference between the given temperature and nearest interval is at
most 9/2 ℉.  Then the conversion is approximated to 1/2 ℃/℉, so we
calculate:

$$
9/2(5/9-1/2) = 0.25℃
$$

## Final thoughts and when not to use it
That's pretty much it.  In summary the conversion is:

* Accurate to within 0.25℃ for any temperature in Fahrenheit, or 0.5℉
  for any temperature in Celsius.
* Simply calculable; you never need to divide by more than 2.
* Gives immediate feedback; at every step you get a temperature which
  is roughly the temperature in Celsius.

If you're converting temperature in the thousands of degrees and
higher, you're better off approximating it by multiplying by 2 to go
from ℃ to ℉.  It's unlikely you want super precise conversions in that
temperature range, and the temperatures essentially have a direct
linear relationship in that range anyway.
