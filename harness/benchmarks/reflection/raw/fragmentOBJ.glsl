precision mediump float;

varying vec3 vPosition;
uniform mat4 uModel;
uniform mat4 uView;
varying vec3 vNormal;
uniform vec4 uLight;

void main() {
    vec3 ambient = vec3(0.1, 0., 0.);
    vec3 diffuse = vec3(0.4, 0.3, 0.9);
    vec3 spec = vec3(1., 1., 1.);
    vec3 lightDir = normalize(vec3(uLight - uModel * vec4(vPosition, 1.)));
    float lambertian = max(dot(normalize(vec3(uModel * vec4(vNormal, 1.))), lightDir), 0.);
    vec3 reflectDir = normalize(vec3(uView * vec4(reflect(-lightDir, normalize(vec3(uModel * vec4(vNormal, 0.)))), 0.)));
    float specular = pow(max(dot(-normalize(vec3(uView * uModel * vec4(vPosition, 1.))), reflectDir), 0.), 32.);
    gl_FragColor = vec4(ambient + lambertian * diffuse + specular * spec, 1.);
}