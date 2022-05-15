---
layout: post
title: A fast, accurate mental method to convert between ℃ and ℉
hasmath: true
date: 2022-05-15 09:04 -0700
---
As a speaker of multiple languages, I'm often aware of how inherent
habits in our speech can greatly influence the extent to which other
people make sense of it.  But even when you speak the same language,
even a topic as simple as the weather can already bring unnecessary
friction to the conversation if the speakers are using incompatible
units.  Or maybe I'm just coming up with an arbitrary reason to
justify this party trick.  In any case, I describe a mental heuristic
that gets you within 0.25 degrees Celsius for any temperature in
Fahrenheit, and prove the error bound.  For the other direction, the
error in converting a temperature in Celsius to Fahrenheit is at most
0.5℉.

First of all, this method is _incremental_.  That is, you get an
immediate sense of the rough temperature in Celsius for a given
temperature in Fahrenheit, and if you do a bit more mental
calculation, then you achieve this error of 0.25.  Fortunately, the
extra work you have to do is just diving a number by 2, and the
largest such number you ever have to divide in half is 5.

## Anchor points
I memorize the following table.  While it may seem a bit daunting at
first, it actually is very simple.  Fahrenheit and Celsius have a
linear relationship, so a difference of 9℉ corresponds to a difference
of 5℃.  If you memorize just one of these numbers (I recommend 50℉
corresponding to 10℃) then you can generate the rest on the go.

| Fahrenheit | Celsius |
|------------|---------|
| **32**     | **0**   |
| 41         | 5       |
| **50**     | **10**  |
| 59         | 15      |
| **68**     | **20**  |
| 77         | 25      |
| **86**     | **30**  |

    
I highlighted the easiest to memorize points.  So, if you ever
encounter any of the temperatures in the table, you have the exact
value in the other unit.  So far so good, but this isn't quite enough.
To approximate the temperature in Celsius even better, I choose the
nearest anchor point in Fahrenheit and interpolate between that point
and our given temperature.  For instance, if I have 72℉, then the
closest memorized point is 68℉, which corresponds to a value of 20℃.
Then I take half of the difference and add it to the temperature in
Celsius, thus we get 22℃ (the true temperature is in fact 22.22℃).

## Code
I can render the above words into code so it's unambiguous what I
actually mean.  Note that in the code I didn't use a lookup table but
instead some arithmetic to find the closest anchor point.  Obviously
in practice it'll be memorized.

```haskell
myConv :: Double -> Double
myConv given = rough + diff
  where
    -- Nearest memorized temperature
    close = round ((given - 5) / 9) * 9 + 5
    -- Convert to Celsius
    rough = fromIntegral (((close - 32) `div` 9) * 5)
    -- Half of the difference
    diff = (given - fromIntegral close) / 2
```

Here's the above code but in Python instead:

```python
def my_conv(given):
    # Nearest memorized temperature
    close = round((given - 5) / 9) * 9 + 5
    # Convert to Celsius
    rough = (close - 32) // 9
    # Half of the difference
    diff = (given - close) / 2
    return rough + diff
```

## Proof of error bound
We show that if we have $$T_F$$, then the error bound for converting
to Celsius is at most 0.25℃.  The calculation is straightforward.
First we observe since the memorized intervals occur every 9℉, the
difference is at most 4.5℉.  Then the conversion is approximated to
1/2℃/℉, so we calculate:

$$
4.5(5/9-1/2) = 0.25
$$

## Final thoughts and when not to use it
Thus we have a method which is:

* Accurate to within 0.25℃ for any temperature in Fahrenheit, or 0.5℉
  for any temperature in Celsius
* Simply calculable; you never need to divide by more than 2.
* Immediate feedback; at every step you get a temperature which is
  roughly the temperature in Celsius.

If you're converting temperature in the thousands of degrees and
higher, you're better off approximating it by multiplying by 2 to go
from ℃ to ℉.  It's unlikely you want super precise conversions in that
temperature range, and the temperatures essentially have a linear
relationship in that range anyway.
