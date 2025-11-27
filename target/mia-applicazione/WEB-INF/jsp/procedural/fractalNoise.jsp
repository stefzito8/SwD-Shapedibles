<%@ page contentType="text/html;charset=UTF-8" %>
<html>
<body>
    <svg width="0" height="0">
        <defs>
            <filter id='fractalNoiseFilter'>
                <feTurbulence
                        type='fractalNoise'
                        baseFrequency='0.7'
                        stitchTiles='stitch'></feTurbulence>
        
                <feBlend in="SourceGraphic" in2="monoNoise" mode="screen"></feBlend>
            </filter>
        </defs>
    </svg>
</body>
</html>
