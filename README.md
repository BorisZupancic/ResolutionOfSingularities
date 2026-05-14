# ResolutionOfSingularities.

This is a SageMath package for performing resolution of singularities, using weighted blowups.
> [!WARNING]
> Actually, `ResolutionOfSingularities` cannot yet perform either of these tasks. 
> What it can do right now is compute the associated center of a subscheme of an affine scheme. 

## Installation
There are two easy ways to intall `ResolutionOfSingularties`. The only dependency is `sage`.

### Option 1: Using `pip`.
Use pip like you usually would:

```bash 
sage -pip install git+github.com/BorisZupancic/ResolutionOfSingularities
```
    
### Option 2: From source
Clone the repo then use pip in the repo directory:
```bash
git clone https://github.com/BorisZupancic/ResolutionOfSingularities
cd ResolutionOfSingularities
sage -pip install -e . 
```

## Basic Usage
Here's a simple example
```python
sage: from ResolutionOfSingularities import *
sage: X.<x,y,z> = AffineSpace(3,QQ)
sage: Y = X.subscheme(x^2 + y^2*z)
sage: Z = global_associated_center(Y); Z
Weighted subscheme of Affine Space of dimension 3 over Rational Field defined by parameters [x, y, z] and invariant [2, 3, 3]
```

## Documentation
For now the docs are not hosted online but, if you installed `ResolutionOfSingularities` from source,
then you can build the docs yourself by running the following from `./ResolutionOfSingularities`:

```bash
make docs
```
