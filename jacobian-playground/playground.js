(function () {
    'use strict';

    var state = { operations: [] };
    var renderFrame = 0;

    var determinantValue = document.getElementById('determinantValue');
    var orientationValue = document.getElementById('orientationValue');
    var depthValue = document.getElementById('depthValue');
    var stepValue = document.getElementById('stepValue');
    var degreeValue = document.getElementById('degreeValue');
    var pipelineExpression = document.getElementById('pipelineExpression');
    var pipelineList = document.getElementById('pipelineList');
    var determinantProof = document.getElementById('determinantProof');
    var controlMessage = document.getElementById('controlMessage');
    var shearAmount = document.getElementById('shearAmount');
    var shearPower = document.getElementById('shearPower');
    var targetDeterminant = document.getElementById('targetDeterminant');
    var zSlice = document.getElementById('zSlice');
    var zValue = document.getElementById('zValue');
    var canvas = document.getElementById('mapCanvas');
    var plotScale = document.getElementById('plotScale');
    var collisionNote = document.getElementById('collisionNote');
    var collisionOutputs = Array.prototype.slice.call(document.querySelectorAll('.collision-image'));
    var context = canvas.getContext('2d');

    function absoluteBigInt(value) { return value < 0n ? -value : value; }

    function gcd(a, b) {
        a = absoluteBigInt(a);
        b = absoluteBigInt(b);
        while (b !== 0n) {
            var next = a % b;
            a = b;
            b = next;
        }
        return a || 1n;
    }

    function rational(numerator, denominator) {
        if (denominator === 0n) throw new Error('A denominator cannot be zero.');
        if (denominator < 0n) {
            numerator = -numerator;
            denominator = -denominator;
        }
        var divisor = gcd(numerator, denominator);
        return { n: numerator / divisor, d: denominator / divisor };
    }

    function decimalRational(text) {
        var sign = text.charAt(0) === '-' ? -1n : 1n;
        var unsigned = text.replace(/^[+-]/, '');
        var parts = unsigned.split('.');
        var whole = parts[0] || '0';
        var fraction = parts[1] || '';
        var denominator = 10n ** BigInt(fraction.length);
        var numerator = BigInt(whole + fraction) * sign;
        return rational(numerator, denominator);
    }

    function parseRational(raw, label) {
        var text = String(raw).trim().replace(/−/g, '-');
        if (!text) throw new Error('Enter ' + label + '.');
        var match = text.match(/^([+-]?(?:\d+(?:\.\d*)?|\.\d+))(?:\/([+-]?(?:\d+(?:\.\d*)?|\.\d+)))?$/);
        if (!match) throw new Error(label + ' must be a number or fraction such as 1/2.');
        var top = decimalRational(match[1]);
        if (!match[2]) return top;
        var bottom = decimalRational(match[2]);
        if (bottom.n === 0n) throw new Error(label + ' cannot have a zero denominator.');
        return rational(top.n * bottom.d, top.d * bottom.n);
    }

    function multiply(a, b) { return rational(a.n * b.n, a.d * b.d); }
    function addRational(a, b) { return rational(a.n * b.d + b.n * a.d, a.d * b.d); }
    function integerRational(value) { return rational(BigInt(value), 1n); }
    function powRational(base, exponent) {
        var result = rational(1n, 1n);
        for (var step = 0; step < exponent; step += 1) result = multiply(result, base);
        return result;
    }
    function divide(a, b) {
        if (b.n === 0n) throw new Error('Cannot divide by a zero determinant.');
        return rational(a.n * b.d, a.d * b.n);
    }
    function rationalNumber(value) { return Number(value.n) / Number(value.d); }
    function rationalText(value) {
        return value.d === 1n ? value.n.toString() : value.n.toString() + '/' + value.d.toString();
    }

    function currentDeterminant() {
        return state.operations.reduce(function (result, operation) {
            return multiply(result, operation.factor);
        }, rational(1n, 1n));
    }

    function baseMap(point) {
        var x = point[0];
        var y = point[1];
        var z = point[2];
        var a = 1 + 2 * x * y;
        var b = 4 + 6 * x * y;
        return [
            Math.pow(a, 3) * z + y * y * a * b,
            y + 6 * x * a * a * z + 6 * x * y * y * b,
            -x + 3 * x * x * y + 2 * x * x * x * z
        ];
    }

    function evaluateMap(point) {
        return state.operations.reduce(function (value, operation) {
            if (operation.type === 'shear12') {
                return [value[0] + operation.amount * Math.pow(value[1], operation.power), value[1], value[2]];
            }
            if (operation.type === 'shear23') {
                return [value[0], value[1] + operation.amount * Math.pow(value[2], operation.power), value[2]];
            }
            if (operation.type === 'compose') return baseMap(value);
            if (operation.type === 'scale') return [operation.amount * value[0], value[1], value[2]];
            return value;
        }, baseMap(point));
    }

    function baseMapExact(point) {
        var x = point[0];
        var y = point[1];
        var z = point[2];
        var xy = multiply(x, y);
        var a = addRational(integerRational(1), multiply(integerRational(2), xy));
        var b = addRational(integerRational(4), multiply(integerRational(6), xy));
        var ySquared = multiply(y, y);
        var xSquared = multiply(x, x);
        var xCubed = multiply(xSquared, x);
        return [
            addRational(multiply(powRational(a, 3), z), multiply(ySquared, multiply(a, b))),
            addRational(y, addRational(
                multiply(integerRational(6), multiply(x, multiply(multiply(a, a), z))),
                multiply(integerRational(6), multiply(x, multiply(ySquared, b)))
            )),
            addRational(multiply(integerRational(-1), x), addRational(
                multiply(integerRational(3), multiply(xSquared, y)),
                multiply(integerRational(2), multiply(xCubed, z))
            ))
        ];
    }

    // Alpöge's three-point collision, in the det-1 coordinates used by G:
    // all three share the image (−1/16, 0, 0) under the base map.
    var witnessPoints = [
        [integerRational(0), integerRational(0), rational(-1n, 16n)],
        [integerRational(1), rational(-3n, 4n), rational(13n, 8n)],
        [integerRational(-1), rational(3n, 4n), rational(13n, 8n)]
    ];

    function evaluateMapExact(point) {
        return state.operations.reduce(function (value, operation) {
            if (operation.type === 'shear12') {
                return [addRational(value[0], multiply(operation.amountExact, powRational(value[1], operation.power))), value[1], value[2]];
            }
            if (operation.type === 'shear23') {
                return [value[0], addRational(value[1], multiply(operation.amountExact, powRational(value[2], operation.power))), value[2]];
            }
            if (operation.type === 'compose') return baseMapExact(value);
            if (operation.type === 'scale') return [multiply(operation.factor, value[0]), value[1], value[2]];
            return value;
        }, baseMapExact(point));
    }

    function pointText(point) {
        return '(' + point.map(rationalText).join(', ') + ')';
    }

    function degreeVector() {
        return state.operations.reduce(function (degrees, operation) {
            var d1 = degrees[0];
            var d2 = degrees[1];
            var d3 = degrees[2];
            if (operation.type === 'shear12') return [Math.max(d1, operation.power * d2), d2, d3];
            if (operation.type === 'shear23') return [d1, Math.max(d2, operation.power * d3), d3];
            if (operation.type === 'compose') {
                return [
                    Math.max(d3 + 3 * (d1 + d2), 2 * d1 + 4 * d2),
                    Math.max(d2, 3 * d1 + 2 * d2 + d3, 2 * d1 + 3 * d2),
                    Math.max(d1, 2 * d1 + d2, 3 * d1 + d3)
                ];
            }
            if (operation.type === 'scale' && operation.factor.n === 0n) return [0, d2, d3];
            return degrees;
        }, [7, 6, 4]);
    }

    function operationNotation(operation) {
        if (operation.type === 'shear12') return 'S₁₂[' + operation.amountLabel + ',' + operation.power + ']';
        if (operation.type === 'shear23') return 'S₂₃[' + operation.amountLabel + ',' + operation.power + ']';
        if (operation.type === 'compose') return 'G';
        return 'D₁[' + operation.amountLabel + ']';
    }

    function orientationText(determinant) {
        if (determinant.n === 0n) return 'singular · dimension collapsed';
        var magnitude = rationalNumber(determinant);
        if (determinant.n < 0n) return 'orientation reversed · scale ' + formatNumber(Math.abs(magnitude));
        if (determinant.n === determinant.d) return 'volume preserving';
        return 'orientation preserved · scale ' + formatNumber(magnitude);
    }

    function formatNumber(value) {
        if (!Number.isFinite(value)) return 'overflow';
        if (Math.abs(value) >= 10000 || (Math.abs(value) > 0 && Math.abs(value) < 0.001)) return value.toExponential(2);
        return Number(value.toPrecision(4)).toString();
    }

    function quantile(sorted, fraction) {
        var position = fraction * (sorted.length - 1);
        var below = Math.floor(position);
        var above = Math.min(below + 1, sorted.length - 1);
        return sorted[below] + (position - below) * (sorted[above] - sorted[below]);
    }

    // High-degree compositions send corner samples astronomically far away; fitting
    // the view to the raw min/max collapses everything else onto a few pixels.
    // Fit the central 2–98% instead and let outlier arcs run off the panel.
    function robustRange(sorted) {
        var low = quantile(sorted, 0.02);
        var high = quantile(sorted, 0.98);
        if (!(high - low > 1e-9)) {
            low = sorted[0];
            high = sorted[sorted.length - 1];
        }
        if (!(high - low > 1e-9)) {
            low -= 1;
            high += 1;
        }
        return [low, high];
    }

    function setMessage(message, isError) {
        controlMessage.textContent = message || '';
        controlMessage.classList.toggle('is-error', Boolean(isError));
    }

    function addOperation(operation, message) {
        if (state.operations.length >= 12) {
            setMessage('The twelve-step limit keeps the live plot responsive. Undo a step to continue.', true);
            return;
        }
        state.operations.push(operation);
        setMessage(message, false);
        render();
    }

    function addShear(type) {
        try {
            var amount = parseRational(shearAmount.value, 'the shear amount');
            var power = Number(shearPower.value);
            addOperation({
                type: type,
                amount: rationalNumber(amount),
                amountExact: amount,
                amountLabel: rationalText(amount),
                power: power,
                factor: rational(1n, 1n),
                name: 'Polynomial shear',
                detail: type === 'shear12'
                    ? 'u₁ ← u₁ + ' + rationalText(amount) + '·u₂^' + power
                    : 'u₂ ← u₂ + ' + rationalText(amount) + '·u₃^' + power
            }, 'Added a determinant-one polynomial shear.');
        } catch (error) {
            setMessage(error.message, true);
        }
    }

    function composeBase() {
        var count = state.operations.filter(function (operation) { return operation.type === 'compose'; }).length;
        if (count >= 3) {
            setMessage('Three extra copies of G are enough for this live preview; the values grow extremely quickly.', true);
            return;
        }
        addOperation({
            type: 'compose',
            factor: rational(1n, 1n),
            name: 'Compose base map G',
            detail: 'F ← G ∘ F'
        }, 'Composed another copy of G; the determinant remains unchanged.');
    }

    function rescale() {
        try {
            var target = parseRational(targetDeterminant.value, 'the target determinant');
            var before = currentDeterminant();
            if (before.n === 0n) {
                if (target.n === 0n) {
                    setMessage('The determinant is already zero.', false);
                } else {
                    setMessage('A singular map cannot reach a nonzero determinant by constant rescaling.', true);
                }
                return;
            }
            var factor = divide(target, before);
            addOperation({
                type: 'scale',
                amount: rationalNumber(factor),
                amountLabel: rationalText(factor),
                factor: factor,
                name: 'Output rescaling',
                detail: 'u₁ ← ' + rationalText(factor) + '·u₁'
            }, target.n === 0n
                ? 'Target zero collapses the first output and makes the map singular.'
                : 'Rescaled output 1; the determinant is now exactly ' + rationalText(target) + '.');
        } catch (error) {
            setMessage(error.message, true);
        }
    }

    function loadDemo() {
        state.operations = [
            { type: 'shear12', amount: 0.5, amountExact: rational(1n, 2n), amountLabel: '1/2', power: 2, factor: rational(1n, 1n), name: 'Polynomial shear', detail: 'u₁ ← u₁ + 1/2·u₂^2' },
            { type: 'compose', factor: rational(1n, 1n), name: 'Compose base map G', detail: 'F ← G ∘ F' },
            { type: 'shear23', amount: -1, amountExact: rational(-1n, 1n), amountLabel: '-1', power: 3, factor: rational(1n, 1n), name: 'Polynomial shear', detail: 'u₂ ← u₂ − u₃^3' },
            { type: 'scale', amount: 6, amountLabel: '6', factor: rational(6n, 1n), name: 'Output rescaling', detail: 'u₁ ← 6·u₁' }
        ];
        targetDeterminant.value = '6';
        setMessage('Loaded a four-stage example with determinant 6.', false);
        render();
    }

    function renderLedger() {
        pipelineList.replaceChildren();
        var stages = [{ name: 'Base map G', detail: 'the pictured polynomial map', factor: rational(1n, 1n) }].concat(state.operations);
        stages.forEach(function (stage) {
            var item = document.createElement('li');
            var name = document.createElement('span');
            name.className = 'pipeline-name';
            name.textContent = stage.name;
            var detail = document.createElement('span');
            detail.className = 'pipeline-detail';
            detail.textContent = stage.detail;
            var factor = document.createElement('span');
            factor.className = 'pipeline-factor';
            factor.textContent = 'det × ' + rationalText(stage.factor);
            item.append(name, detail, factor);
            pipelineList.append(item);
        });

        var notation = state.operations.slice().reverse().map(operationNotation);
        notation.push('G');
        pipelineExpression.textContent = 'F = ' + notation.join(' ∘ ');

        var factors = stages.map(function (stage) { return rationalText(stage.factor); });
        determinantProof.textContent = state.operations.length
            ? 'det J_F = ' + factors.join(' × ') + ' = ' + rationalText(currentDeterminant())
            : 'det J_F = 1';
    }

    function renderCollision() {
        if (!collisionNote || collisionOutputs.length !== witnessPoints.length) return;
        var images = witnessPoints.map(evaluateMapExact).map(pointText);
        collisionOutputs.forEach(function (element, index) { element.textContent = images[index]; });
        var identical = images.every(function (text) { return text === images[0]; });
        var determinant = currentDeterminant();
        if (!identical) {
            collisionNote.textContent = 'The images differ — this would be a bug in the playground, not in the mathematics.';
            return;
        }
        collisionNote.textContent = determinant.n === 0n
            ? 'All three images still agree — and rescaling to zero has made the map singular on top of it.'
            : 'All three images agree while det J_F = ' + rationalText(determinant) +
              ' everywhere: a nonzero constant determinant without injectivity.';
    }

    function renderStats() {
        var determinant = currentDeterminant();
        var degrees = degreeVector();
        var depth = 1 + state.operations.filter(function (operation) { return operation.type === 'compose'; }).length;
        determinantValue.textContent = rationalText(determinant);
        determinantValue.title = rationalText(determinant);
        orientationValue.textContent = orientationText(determinant);
        depthValue.textContent = String(depth);
        stepValue.textContent = state.operations.length
            ? state.operations.length + (state.operations.length === 1 ? ' added step' : ' added steps')
            : 'base map only';
        degreeValue.textContent = String(Math.max.apply(null, degrees));
    }

    function cssColor(name) {
        return getComputedStyle(document.documentElement).getPropertyValue(name).trim();
    }

    function sampleGrid(z) {
        var extent = 0.42;
        var lineCount = 9;
        var samples = 58;
        var horizontal = [];
        var vertical = [];

        for (var line = 0; line < lineCount; line += 1) {
            var fixed = -extent + (2 * extent * line) / (lineCount - 1);
            var horizontalLine = [];
            var verticalLine = [];
            for (var sample = 0; sample < samples; sample += 1) {
                var moving = -extent + (2 * extent * sample) / (samples - 1);
                var h = evaluateMap([moving, fixed, z]);
                var v = evaluateMap([fixed, moving, z]);
                horizontalLine.push([h[0], h[1]]);
                verticalLine.push([v[0], v[1]]);
            }
            horizontal.push(horizontalLine);
            vertical.push(verticalLine);
        }
        return { horizontal: horizontal, vertical: vertical };
    }

    function drawPlot() {
        renderFrame = 0;
        var rect = canvas.getBoundingClientRect();
        var ratio = Math.min(window.devicePixelRatio || 1, 2);
        var width = Math.max(320, Math.round(rect.width * ratio));
        var height = Math.max(300, Math.round(rect.height * ratio));
        if (canvas.width !== width || canvas.height !== height) {
            canvas.width = width;
            canvas.height = height;
        }

        context.clearRect(0, 0, width, height);
        var z = Number(zSlice.value);
        var grid = sampleGrid(z);
        var allPoints = grid.horizontal.concat(grid.vertical).reduce(function (points, line) {
            return points.concat(line);
        }, []).filter(function (point) {
            return point.every(function (value) { return Number.isFinite(value) && Math.abs(value) < 1e150; });
        });

        if (!allPoints.length) {
            plotScale.textContent = 'numeric overflow — undo a composition';
            return;
        }

        var xs = allPoints.map(function (point) { return point[0]; }).sort(function (a, b) { return a - b; });
        var ys = allPoints.map(function (point) { return point[1]; }).sort(function (a, b) { return a - b; });

        // Deep compositions spread samples across many orders of magnitude, so
        // even a percentile fit collapses the interesting structure. When the
        // 2–98% span dwarfs the interquartile core, compress each axis with
        // asinh: linear near the bulk of the data, logarithmic in the tails.
        function spreadRatio(sorted) {
            var core = quantile(sorted, 0.75) - quantile(sorted, 0.25);
            var full = quantile(sorted, 0.98) - quantile(sorted, 0.02);
            return full / Math.max(core, 1e-12);
        }
        function warpScale(sorted) {
            return Math.max(Math.abs(quantile(sorted, 0.25)), Math.abs(quantile(sorted, 0.75)), 1e-9);
        }
        var warped = Math.max(spreadRatio(xs), spreadRatio(ys)) > 25;
        var warpX = warped ? warpScale(xs) : 1;
        var warpY = warped ? warpScale(ys) : 1;
        function warp(value, unit) { return warped ? Math.asinh(value / unit) : value; }

        var xRange = robustRange(xs.map(function (value) { return warp(value, warpX); }));
        var yRange = robustRange(ys.map(function (value) { return warp(value, warpY); }));
        var rangeX = xRange[1] - xRange[0];
        var rangeY = yRange[1] - yRange[0];
        var padding = 34 * ratio;
        var scale = Math.min((width - 2 * padding) / rangeX, (height - 2 * padding) / rangeY);
        var centerX = (xRange[0] + xRange[1]) / 2;
        var centerY = (yRange[0] + yRange[1]) / 2;
        var coordinateLimit = 40 * Math.max(width, height);

        function project(point) {
            return [
                width / 2 + (warp(point[0], warpX) - centerX) * scale,
                height / 2 - (warp(point[1], warpY) - centerY) * scale
            ];
        }

        function strokeLines(lines, color) {
            lines.forEach(function (line, index) {
                context.beginPath();
                var penDown = false;
                line.forEach(function (point) {
                    if (!Number.isFinite(point[0]) || !Number.isFinite(point[1])) {
                        penDown = false;
                        return;
                    }
                    var projected = project(point);
                    // Extremely distant samples would feed the rasterizer absurd
                    // coordinates; break the polyline instead of drawing to them.
                    if (Math.abs(projected[0]) > coordinateLimit || Math.abs(projected[1]) > coordinateLimit) {
                        penDown = false;
                        return;
                    }
                    if (penDown) context.lineTo(projected[0], projected[1]);
                    else {
                        context.moveTo(projected[0], projected[1]);
                        penDown = true;
                    }
                });
                context.globalAlpha = index === 4 ? 0.95 : 0.62;
                context.lineWidth = (index === 4 ? 1.8 : 1.05) * ratio;
                context.strokeStyle = color;
                context.stroke();
            });
        }

        context.lineJoin = 'round';
        context.lineCap = 'round';
        strokeLines(grid.horizontal, cssColor('--accent'));
        strokeLines(grid.vertical, cssColor('--cyan'));
        context.globalAlpha = 1;

        var beyondView = allPoints.filter(function (point) {
            var projected = project(point);
            return projected[0] < 0 || projected[0] > width || projected[1] < 0 || projected[1] > height;
        }).length;
        var xLabelRange = robustRange(xs);
        var yLabelRange = robustRange(ys);
        plotScale.textContent = (warped ? 'asinh-compressed view · ' : '')
            + 'u₁ ' + formatNumber(xLabelRange[0]) + '…' + formatNumber(xLabelRange[1])
            + ' · u₂ ' + formatNumber(yLabelRange[0]) + '…' + formatNumber(yLabelRange[1])
            + (beyondView ? ' · ' + beyondView + ' of ' + allPoints.length + ' beyond view' : '');
        canvas.setAttribute('aria-label', 'Deformed coordinate grid at z equals ' + z.toFixed(2) + '; the composed map has constant Jacobian determinant ' + rationalText(currentDeterminant()));
    }

    function queuePlot() {
        if (renderFrame) cancelAnimationFrame(renderFrame);
        renderFrame = requestAnimationFrame(drawPlot);
    }

    function render() {
        renderStats();
        renderLedger();
        renderCollision();
        zValue.textContent = Number(zSlice.value).toFixed(2);
        queuePlot();
    }

    document.querySelectorAll('[data-action]').forEach(function (button) {
        button.addEventListener('click', function () {
            var action = button.getAttribute('data-action');
            if (action === 'shear12' || action === 'shear23') addShear(action);
            else if (action === 'compose') composeBase();
            else if (action === 'rescale') rescale();
            else if (action === 'demo') loadDemo();
            else if (action === 'undo') {
                if (state.operations.length) {
                    state.operations.pop();
                    setMessage('Removed the most recent step.', false);
                    render();
                } else setMessage('There is no added step to undo.', false);
            } else if (action === 'reset') {
                state.operations = [];
                setMessage('Returned to the base map G.', false);
                render();
            }
        });
    });

    // The z-slider only moves the plotted slice; skip rebuilding the ledger DOM.
    zSlice.addEventListener('input', function () {
        zValue.textContent = Number(zSlice.value).toFixed(2);
        queuePlot();
    });

    shearAmount.addEventListener('keydown', function (event) {
        if (event.key === 'Enter') addShear('shear12');
    });
    targetDeterminant.addEventListener('keydown', function (event) {
        if (event.key === 'Enter') rescale();
    });

    var themeToggle = document.getElementById('themeToggle');
    var themeLabel = document.getElementById('themeLabel');
    function syncThemeLabel() {
        if (themeLabel) themeLabel.textContent = document.documentElement.getAttribute('data-theme') === 'dark' ? 'Light' : 'Dark';
    }
    if (themeToggle) {
        syncThemeLabel();
        themeToggle.addEventListener('click', function () {
            var current = document.documentElement.getAttribute('data-theme');
            var next = current === 'dark' ? 'light' : 'dark';
            document.documentElement.setAttribute('data-theme', next);
            try { localStorage.setItem('theme', next); } catch (error) {}
            syncThemeLabel();
            queuePlot();
        });
    }

    if ('ResizeObserver' in window) new ResizeObserver(queuePlot).observe(canvas);
    else window.addEventListener('resize', queuePlot);

    // Inert in browsers; lets a headless harness exercise the real internals.
    if (typeof window !== 'undefined' && typeof window.__playgroundTestHook === 'function') {
        window.__playgroundTestHook({
            state: state,
            rational: rational,
            rationalText: rationalText,
            parseRational: parseRational,
            baseMap: baseMap,
            baseMapExact: baseMapExact,
            evaluateMap: evaluateMap,
            evaluateMapExact: evaluateMapExact,
            witnessPoints: witnessPoints,
            currentDeterminant: currentDeterminant,
            degreeVector: degreeVector,
            quantile: quantile,
            robustRange: robustRange,
            loadDemo: loadDemo,
            composeBase: composeBase,
            rescale: rescale,
            drawPlot: drawPlot,
            render: render
        });
    }

    render();
})();
